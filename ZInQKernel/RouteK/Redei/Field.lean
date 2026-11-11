import ZInQKernel.RouteK.Rank5b.Sec3.RedeiStatement

/-!
# Rédei's formula, step 1: the field `ℚ(√−n)` (`docs/research/redei-plan.md` §3.2)

`K = QNeg n = ℚ(ω)`, `ω² = −n` (from `Rank5b/Sec3/RedeiStatement.lean`), `O = 𝓞 K`, and `σ` the
nontrivial automorphism (any `σ : K ≃ₐ[ℚ] K` with `σ ≠ 1`).

* instances: `Field`, `NumberField`, `IsGalois ℚ K`, `Fintype (ClassGroup O)`; `card_gal`;
* `isIntegral_omega`, `isIntegral_theta` (`n ≡ 3 (mod 4)`);
* `conj_omega : σ ω = −ω`, `conj_apply : σ x = star x`, `conj_unique`;
* `algNorm_eq`, `norm_eq_mul_conj`, `norm_nonneg`; for integral elements `algNorm_coe`,
  `normZ_nonneg`, `normZ_omega`, `normZ_natCast`, `normZ_intCast`;
* `O ∩ ℚ = ℤ` (`exists_int_of_coe_eq_algebraMap`), `intCast_dvd_intCast_iff`, the rational units of
  `O` are `±1` (`isUnit_intCast_iff`, `rat_unit_eq`), `span_natCast_eq_span_natCast_iff`.
-/

noncomputable section

open NumberField Pointwise
open scoped nonZeroDivisors

namespace ZInQ.RouteK.Redei

open ZInQ.RouteK.Rank5b

section Field

variable (n : ℕ) [NeZero n]

local notation "K" => QNeg n
local notation "O" => 𝓞 (QNeg n)
local notation "ω" => (QuadraticAlgebra.omega : QNeg n)

example : Field K := inferInstance
example : CharZero K := inferInstance
example : FiniteDimensional ℚ K := inferInstance
example : NumberField K := inferInstance
example : IsGalois ℚ K := inferInstance
example : Fintype (ClassGroup O) := inferInstance

theorem card_gal : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, QuadraticAlgebra.finrank_eq_two]

theorem omega_sq : ω * ω = algebraMap ℚ K (-(n : ℚ)) := by
  rw [QuadraticAlgebra.omega_mul_omega_eq_algebraMap]; simp

/-- `ω = √−n` is an algebraic integer. -/
theorem isIntegral_omega : IsIntegral ℤ ω := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  have h : ω ^ 2 = algebraMap ℤ K (-(n : ℤ)) := by
    rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  rw [h]
  exact isIntegral_algebraMap

/-- `ω` as an element of `O`. -/
abbrev omegaO : O := ⟨ω, isIntegral_omega n⟩

@[simp] theorem algebraMap_omegaO : algebraMap O K (omegaO n) = ω := rfl

@[simp] theorem coe_omegaO : ((omegaO n : O) : K) = ω := rfl

theorem omegaO_sq : omegaO n * omegaO n = -(n : O) := by
  apply RingOfIntegers.ext; simp only [map_mul, algebraMap_omegaO, omega_sq, map_neg, map_natCast]

theorem theta_eq : ((1 + ω) / 2 : K) = ⟨1 / 2, 1 / 2⟩ := by
  rw [div_eq_iff (two_ne_zero)]
  ext <;> simp [QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

/-- `θ = (1 + √−n)/2` is an algebraic integer when `n ≡ 3 (mod 4)`. -/
theorem isIntegral_theta (h3 : n % 4 = 3) : IsIntegral ℤ ((1 + ω) / 2 : K) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n + 1 = 4 * m := ⟨(n + 1) / 4, by omega⟩
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩
  · have : (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ)).natDegree = 2 := by
      compute_degree!
    refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one 2 this.le ?_
    simp [Polynomial.coeff_X]
  · have hmq : (n : ℚ) + 1 = 4 * m := by exact_mod_cast hm
    rw [theta_eq]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    ext
    · simp [pow_two]; linarith
    · simp [pow_two]; ring

/-- `θ` as an element of `O` (for `n ≡ 3 (mod 4)`). -/
abbrev thetaO (h3 : n % 4 = 3) : O := ⟨(1 + ω) / 2, isIntegral_theta n h3⟩

@[simp] theorem algebraMap_thetaO (h3 : n % 4 = 3) :
    algebraMap O K (thetaO n h3) = (1 + ω) / 2 := rfl

theorem two_mul_thetaO (h3 : n % 4 = 3) : 2 * thetaO n h3 = 1 + omegaO n := by
  apply RingOfIntegers.ext
  simp only [map_mul, map_add, map_one, map_ofNat, algebraMap_thetaO, algebraMap_omegaO]
  field_simp

/-! ### The nontrivial automorphism -/

variable {n}

theorem conj_omega (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) : σ ω = -ω := by
  set z := σ ω with hz
  have htr : QuadraticAlgebra.trace z = 0 :=
    QuadraticAlgebra.trace_algHom_omega (σ : K →ₐ[ℚ] K) σ.injective
  have hno : QuadraticAlgebra.norm z = -(-(n : ℚ)) :=
    QuadraticAlgebra.norm_algHom_omega (σ : K →ₐ[ℚ] K) σ.injective
  rw [QuadraticAlgebra.trace_def] at htr
  rw [QuadraticAlgebra.norm_def] at hno
  have hre : z.re = 0 := by simpa using htr
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have him : z.im * z.im = 1 := by
    rw [hre] at hno
    have : (n : ℚ) * (z.im * z.im) = n * 1 := by linear_combination hno
    exact mul_left_cancel₀ hn0 this
  have him' : z.im = 1 ∨ z.im = -1 := by
    have : (z.im - 1) * (z.im + 1) = 0 := by linear_combination him
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases him' with h1 | h1
  · exfalso
    apply hσ
    have hzω : z = ω := by
      ext <;> simp [hre, h1, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]
    have : σ.toAlgHom = (AlgHom.id ℚ K) :=
      QuadraticAlgebra.algHom_ext (by simpa using hzω)
    exact AlgEquiv.ext fun x => congrArg (fun f : K →ₐ[ℚ] K => f x) this
  · ext <;> simp [hre, h1, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]

/-- The nontrivial automorphism is the conjugation `star`. -/
theorem conj_apply (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (x : K) : σ x = star x := by
  conv_lhs => rw [← QuadraticAlgebra.re_smul_add_im_smul x]
  rw [map_add, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, AlgEquiv.commutes,
    AlgEquiv.commutes, map_one, conj_omega σ hσ]
  ext <;> simp [QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]

/-- There is only one nontrivial automorphism. -/
theorem conj_unique {σ τ : K ≃ₐ[ℚ] K} (hσ : σ ≠ 1) (hτ : τ ≠ 1) : σ = τ := by
  exact AlgEquiv.ext fun x => by rw [conj_apply σ hσ, conj_apply τ hτ]

theorem conj_conj (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (x : K) : σ (σ x) = x := by
  rw [conj_apply σ hσ, conj_apply σ hσ, star_star]

theorem conj_mul_self (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) : σ * σ = 1 := by
  exact AlgEquiv.ext fun x => conj_conj σ hσ x

/-- The two automorphisms are `1` and `σ`. -/
theorem eq_one_or_eq_conj (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (τ : K ≃ₐ[ℚ] K) : τ = 1 ∨ τ = σ := by
  by_cases h : τ = 1
  · exact Or.inl h
  · exact Or.inr (conj_unique h hσ)

/-- A nontrivial automorphism exists. -/
theorem exists_conj_ne_one : ∃ σ : K ≃ₐ[ℚ] K, σ ≠ 1 := by
  by_contra h
  push Not at h
  have : Nat.card (K ≃ₐ[ℚ] K) = 1 := Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => by
    rw [h a, h b]⟩, ⟨1⟩⟩
  rw [card_gal] at this
  exact absurd this (by norm_num)

@[simp] theorem algebraMap_smul (σ : K ≃ₐ[ℚ] K) (x : O) :
    algebraMap O K (σ • x) = σ (algebraMap O K x) := rfl

theorem conj_omegaO (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) : σ • omegaO n = -omegaO n := by
  apply RingOfIntegers.ext
  simp only [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul, algebraMap_omegaO, map_neg]
  exact conj_omega σ hσ

/-! ### Norms -/

variable (n) in
/-- `Algebra.norm` is Mathlib's explicit quadratic norm. -/
theorem algNorm_eq (x : K) : Algebra.norm ℚ x = QuadraticAlgebra.norm x := by
  rw [Algebra.norm_apply]
  exact QuadraticAlgebra.det_toLinearMap_eq_norm x

variable (n) in
/-- The norm of `ℚ(√−n)/ℚ` is `x σ(x)`. -/
theorem norm_eq_mul_conj (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (x : K) :
    algebraMap ℚ K (Algebra.norm ℚ x) = x * σ x := by
  rw [algNorm_eq n, QuadraticAlgebra.algebraMap_norm_eq_mul_star, conj_apply σ hσ]

variable (n) in
theorem norm_nonneg (x : K) : 0 ≤ Algebra.norm ℚ x := by
  rw [algNorm_eq, QuadraticAlgebra.norm_def]
  have h0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_self_nonneg x.re, mul_self_nonneg x.im, mul_nonneg h0 (mul_self_nonneg x.im)]

/-- Norms of integral elements are integers. -/
theorem algNorm_coe (x : O) : Algebra.norm ℚ (x : K) = (Algebra.norm ℤ x : ℚ) :=
  (Algebra.coe_norm_int x).symm

theorem normZ_nonneg (x : O) : 0 ≤ Algebra.norm ℤ x := by
  have := norm_nonneg n (x : K)
  rw [algNorm_coe] at this
  exact_mod_cast this

/-- `N(x)` and `x σ(x)` in `O`. -/
theorem normZ_eq_mul_conj (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (x : O) :
    ((Algebra.norm ℤ x : ℤ) : O) = x * σ • x := by
  apply RingOfIntegers.ext
  have h := norm_eq_mul_conj n σ hσ (x : K)
  rw [algNorm_coe] at h
  simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, algebraMap_smul, map_intCast] at h ⊢
  rw [← h]

theorem finrank_int : Module.finrank ℤ O = 2 := by
  rw [RingOfIntegers.rank, QuadraticAlgebra.finrank_eq_two]

theorem normZ_intCast (m : ℤ) : Algebra.norm ℤ (m : O) = m ^ 2 := by
  have := Algebra.norm_algebraMap (R := ℤ) (S := O) m
  rw [finrank_int] at this
  simpa using this

theorem normZ_natCast (m : ℕ) : Algebra.norm ℤ (m : O) = (m : ℤ) ^ 2 := by
  have := normZ_intCast (n := n) (m : ℤ)
  simpa using this

theorem normZ_omega : Algebra.norm ℤ (omegaO n) = n := by
  have h := algNorm_coe (n := n) (omegaO n)
  rw [coe_omegaO, algNorm_eq n, QuadraticAlgebra.norm_def] at h
  simp [QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega] at h
  exact_mod_cast h.symm

theorem normZ_one_add_omega : Algebra.norm ℤ (1 + omegaO n) = 1 + n := by
  have h := algNorm_coe (n := n) (1 + omegaO n)
  have e : ((1 + omegaO n : O) : K) = 1 + ω := by simp [RingOfIntegers.coe_eq_algebraMap]
  rw [e, algNorm_eq n, QuadraticAlgebra.norm_def] at h
  simp [QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one] at h
  exact_mod_cast h.symm

/-! ### `O ∩ ℚ = ℤ` and the rational units -/

/-- `O ∩ ℚ = ℤ`. -/
theorem exists_int_of_coe_eq_algebraMap (x : O) (q : ℚ) (h : (x : K) = algebraMap ℚ K q) :
    ∃ m : ℤ, q = m := by
  have hx : IsIntegral ℤ (algebraMap ℚ K q) := h ▸ x.2
  have hq : IsIntegral ℤ q :=
    (isIntegral_algHom_iff ((Algebra.ofId ℚ K).restrictScalars ℤ)
      (algebraMap ℚ K).injective).1 hx
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
  exact ⟨m, by rw [← hm]; simp⟩

theorem intCast_injective : Function.Injective (fun m : ℤ => (m : O)) := by
  intro a b h
  have : ((a : O) : K) = ((b : O) : K) := congrArg _ h
  simpa using this

theorem intCast_dvd_intCast_iff (a b : ℤ) : (a : O) ∣ (b : O) ↔ a ∣ b := by
  constructor
  · rintro ⟨y, hy⟩
    by_cases ha : a = 0
    · subst ha
      have : (b : O) = ((0 : ℤ) : O) := by simpa using hy
      rw [intCast_injective this]
    · have hK : (y : K) = algebraMap ℚ K ((b : ℚ) / a) := by
        have h1 : ((b : O) : K) = ((a : O) : K) * (y : K) := by rw [hy]; simp
        have haK : ((a : ℚ) : K) ≠ 0 := by exact_mod_cast ha
        simp only [map_intCast] at h1
        rw [map_div₀, map_intCast, map_intCast, eq_div_iff (by exact_mod_cast ha), h1, mul_comm]
      obtain ⟨m, hm⟩ := exists_int_of_coe_eq_algebraMap y _ hK
      refine ⟨m, ?_⟩
      have : (b : ℚ) = a * m := by
        rw [← hm]; field_simp
      exact_mod_cast this
  · exact fun h => Int.cast_dvd_cast _ _ h

/-- The rational integers that are units of `O` are `±1`. -/
theorem isUnit_intCast_iff (m : ℤ) : IsUnit (m : O) ↔ m = 1 ∨ m = -1 := by
  rw [isUnit_iff_dvd_one, ← Int.cast_one, intCast_dvd_intCast_iff, ← isUnit_iff_dvd_one,
    Int.isUnit_iff]

/-- The rational units of `O` are `±1`. -/
theorem rat_unit_eq (u : Oˣ) (q : ℚ) (h : ((u : O) : K) = algebraMap ℚ K q) :
    q = 1 ∨ q = -1 := by
  obtain ⟨m, rfl⟩ := exists_int_of_coe_eq_algebraMap (u : O) q h
  have hu : (u : O) = (m : O) := by apply RingOfIntegers.ext; simpa using h
  have := (isUnit_intCast_iff (n := n) m).1 (hu ▸ u.isUnit)
  rcases this with rfl | rfl <;> simp

theorem natCast_dvd_natCast_iff (a b : ℕ) : (a : O) ∣ (b : O) ↔ a ∣ b := by
  have := intCast_dvd_intCast_iff (n := n) a b
  simpa [Int.natCast_dvd_natCast] using this

theorem span_natCast_eq_span_natCast_iff (a b : ℕ) :
    Ideal.span {(a : O)} = Ideal.span {(b : O)} ↔ a = b := by
  constructor
  · intro h
    rw [Ideal.span_singleton_eq_span_singleton] at h
    exact Nat.dvd_antisymm ((natCast_dvd_natCast_iff a b).1 h.dvd)
      ((natCast_dvd_natCast_iff b a).1 h.symm.dvd)
  · rintro rfl; rfl

end Field

end ZInQ.RouteK.Redei
