import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.WeakWeil

/-!
# Rational modular parametrizations in `q`-expansion form

The algebraic curve `X₀(M)` over `ℚ` and its Jacobian are not available as schemes in this
edition. This file fixes the concrete algebraic stand-in used by the printed leaf
`Shimura1973Thm1RationalGamma0` (`Leaves.lean`): the function field of the standard model of
`X₀(M)` over `ℚ`, embedded in `ℚ((q))` by the `q`-expansion at the rational cusp `∞`, is
`ℚ(j(q), j(q^M))`. A `ℚ`-morphism `X₀(M) → A` to an elliptic curve `A/ℚ` is then a solution
`(x, y)` of the Weierstrass equation of `A` in that field, and the pull-back of the invariant
differential `ω_A = dx/(2y + a₁x + a₃)` is computed formally with the Euler operator `θ = q d/dq`
(`dq/q = 2πi dτ`).

## Definitions (written fresh)

* `eisensteinE4Q`, `eisensteinE6Q`: `E₄ = 1 + 240 Σ σ₃(n) qⁿ`, `E₆ = 1 − 504 Σ σ₅(n) qⁿ` over `ℚ`.
* `jInvariantQ`: `j = 1728 E₄³/(E₄³ − E₆²)` in the field `ℚ((q))` (classically `q⁻¹ + 744 + ⋯`;
  this is `j = 1728 g₂³/(g₂³ − 27 g₃²)` for the lattice `ℤ + ℤτ`, written through `E₄`, `E₆`).
* `qPow M`: the substitution `q ↦ q^M` on `ℚ((q))`.
* `modularFunctionFieldQ M`: `ℚ(j(q), j(q^M)) ⊆ ℚ((q))`.
* `eulerOp`: `θ = q d/dq`, coefficientwise `n · a_n`.
* `toComplexLaurent`: the coefficientwise inclusion `ℚ((q)) → ℂ((q))`.
* `IsModularPointQ M A x y`: `x, y ∈ ℚ(j, j_M)`, `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`, and `x`
  is not a constant (some coefficient of `x` away from `q⁰` is nonzero).
* `PullbackIsMultiple A x y ĝ c`: `θx = c · ĝ · (2y + a₁x + a₃)` in `ℂ((q))`, i.e. the pull-back
  of `ω_A` is `c · g(q) dq/q = c · 2πi g(τ) dτ`, where `ĝ` is the `q`-expansion of `g`.

## Proved here

* `jInvariantQ_not_const`, `jInvariantQ_mem`: `j` is a nonconstant element of `ℚ(j, j_M)`
  (non-degeneracy of the definitions: `E₄³ − E₆² = 1728 q + O(q²) ≠ 0`).
* `ne_zero_of_pullbackIsMultiple`: for nonconstant `x` the scalar is nonzero.
* **`exists_rat_eq_of_pullbackIsMultiple`** (rationality of the pull-back scalar): if `x` is not
  constant and `ĝ` has rational coefficients `b` with `b 1 = 1`, then every `c` with
  `PullbackIsMultiple A x y ĝ c` is rational. The proof compares one nonzero coefficient of the
  rational series `ĝ · (2y + a₁x + a₃)` with the corresponding rational coefficient of `θx`; it
  uses neither a Néron model nor a Manin constant.

Classification: definitions and PROVED theorems. That `modularFunctionFieldQ M` is the function
field of the standard model of `X₀(M)` over `ℚ` (with the `q`-expansion at `∞`), and that the formal
`θ` computes pull-backs of differentials, are translation steps used by the leaf and by the
named step `ParametrizationPeriodsGlue` (`Glue.lean`); they are not proved here.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.NewformPeriods

open PowerSeries HahnSeries

/-! ### `E₄`, `E₆` and `j` over `ℚ` -/

/-- `E₄ = 1 + 240 Σ_{n ≥ 1} σ₃(n) qⁿ` with rational coefficients. -/
def eisensteinE4Q : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℚ)

/-- `E₆ = 1 − 504 Σ_{n ≥ 1} σ₅(n) qⁿ` with rational coefficients. -/
def eisensteinE6Q : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℚ)

/-- The `q`-expansion of the modular invariant, `j = 1728 E₄³/(E₄³ − E₆²)`, in `ℚ((q))`. -/
def jInvariantQ : LaurentSeries ℚ :=
  1728 * (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q) ^ 3 /
    ((HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q) ^ 3 -
      (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE6Q) ^ 2)

/-- The substitution `q ↦ q^M` on `ℚ((q))` (`M > 0`). -/
def qPow (M : ℕ) [NeZero M] : LaurentSeries ℚ →+* LaurentSeries ℚ :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (M : ℤ))
    (mul_right_injective₀ (by exact_mod_cast NeZero.ne M))
    (fun _ _ => mul_le_mul_iff_of_pos_left (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)))

/-- **The function field of `X₀(M)` over `ℚ`** in its `q`-expansion form: `ℚ(j(q), j(q^M))`
inside `ℚ((q))`. -/
def modularFunctionFieldQ (M : ℕ) [NeZero M] : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ {jInvariantQ, qPow M jInvariantQ}

/-! ### Non-degeneracy of `j` -/

theorem eisenstein_disc_coeff_one :
    PowerSeries.coeff 1 (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2) = 1728 := by
  simp [eisensteinE4Q, eisensteinE6Q, pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
    ArithmeticFunction.sigma_apply]
  norm_num

theorem eisenstein_disc_coeff_zero :
    PowerSeries.coeff 0 (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2) = 0 := by
  simp [eisensteinE4Q, eisensteinE6Q, pow_succ]

theorem eisenstein_num_coeff_zero : PowerSeries.coeff 0 (1728 * eisensteinE4Q ^ 3) = 1728 := by
  simp [eisensteinE4Q, pow_succ, PowerSeries.coeff_mul]

/-- **`j` is not a constant** (PROVED): `E₄³ − E₆² = 1728 q + O(q²)` is nonzero with zero constant
term while `1728 E₄³` has constant term `1728`. So `ℚ(j, j_M)` is a genuine function field, not `ℚ`,
and the junk value of division by zero does not occur in `jInvariantQ`. -/
theorem jInvariantQ_not_const : jInvariantQ ∉ Set.range (algebraMap ℚ (LaurentSeries ℚ)) := by
  rintro ⟨a, ha⟩
  have hD : (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q) ^ 3 -
      (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE6Q) ^ 2 =
      HahnSeries.ofPowerSeries ℤ ℚ (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2) := by
    rw [map_sub, map_pow, map_pow]
  have hD0 : HahnSeries.ofPowerSeries ℤ ℚ (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun z : LaurentSeries ℚ => z.coeff ((1 : ℕ) : ℤ)) h0
    simp only [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.coeff_zero,
      eisenstein_disc_coeff_one] at h1
    norm_num at h1
  have hN : (1728 : LaurentSeries ℚ) * (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q) ^ 3 =
      HahnSeries.ofPowerSeries ℤ ℚ (1728 * eisensteinE4Q ^ 3) := by
    rw [map_mul, map_pow, map_ofNat]
  have hj : jInvariantQ * HahnSeries.ofPowerSeries ℤ ℚ (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2) =
      HahnSeries.ofPowerSeries ℤ ℚ (1728 * eisensteinE4Q ^ 3) := by
    rw [jInvariantQ, hD, div_mul_cancel₀ _ hD0, hN]
  rw [← ha, HahnSeries.algebraMap_apply', ← map_mul] at hj
  have h1 := congrArg (PowerSeries.coeff 0) (HahnSeries.ofPowerSeries_injective hj)
  rw [eisenstein_num_coeff_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2),
    eisenstein_disc_coeff_zero, mul_zero] at h1
  norm_num at h1

theorem jInvariantQ_mem (M : ℕ) [NeZero M] : jInvariantQ ∈ modularFunctionFieldQ M :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)

/-! ### Euler operator and coefficient map -/

/-- The Euler operator `θ = q d/dq` on `ℚ((q))`: `θ (Σ aₙ qⁿ) = Σ n aₙ qⁿ`. -/
def eulerOp (x : LaurentSeries ℚ) : LaurentSeries ℚ where
  coeff n := (n : ℚ) * x.coeff n
  isPWO_support' := x.isPWO_support.mono fun n hn => by
    simp only [Function.mem_support] at hn ⊢
    exact right_ne_zero_of_mul hn

@[simp]
theorem eulerOp_coeff (x : LaurentSeries ℚ) (n : ℤ) : (eulerOp x).coeff n = (n : ℚ) * x.coeff n :=
  rfl

/-- The coefficientwise inclusion `ℚ((q)) → ℂ((q))`. -/
def toComplexLaurent (x : LaurentSeries ℚ) : LaurentSeries ℂ :=
  x.map (algebraMap ℚ ℂ)

@[simp]
theorem toComplexLaurent_coeff (x : LaurentSeries ℚ) (n : ℤ) :
    (toComplexLaurent x).coeff n = ((x.coeff n : ℚ) : ℂ) := by
  simp [toComplexLaurent]

theorem toComplexLaurent_injective : Function.Injective toComplexLaurent := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
  simpa using this

theorem toComplexLaurent_mul (x y : LaurentSeries ℚ) :
    toComplexLaurent (x * y) = toComplexLaurent x * toComplexLaurent y := by
  unfold toComplexLaurent
  exact HahnSeries.map_mul ((algebraMap ℚ ℂ : ℚ →+* ℂ) : ℚ →ₙ+* ℂ)

theorem toComplexLaurent_ofPowerSeries (b : ℕ → ℚ) :
    toComplexLaurent (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk b)) =
      HahnSeries.ofPowerSeries ℤ ℂ ((PowerSeries.mk b).map (algebraMap ℚ ℂ)) := by
  ext n
  rw [toComplexLaurent_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs <;> simp

@[simp]
theorem toComplexLaurent_zero : toComplexLaurent 0 = 0 := by
  ext n
  simp

/-! ### Modular points and the pull-back of the invariant differential -/

/-- The constant Laurent series with value `a`. -/
abbrev cQ (a : ℚ) : LaurentSeries ℚ := algebraMap ℚ (LaurentSeries ℚ) a

/-- **A `ℚ`-rational point of `A` over the function field of `X₀(M)`**, i.e. a nonconstant
`ℚ`-morphism `X₀(M) → A` in coordinates: `x, y ∈ ℚ(j, j_M)` satisfy the Weierstrass equation of
`A`, and `x` is not constant (some coefficient of `x` at a nonzero exponent is nonzero). -/
def IsModularPointQ (M : ℕ) [NeZero M] (A : WeierstrassCurve ℚ) (x y : LaurentSeries ℚ) : Prop :=
  x ∈ modularFunctionFieldQ M ∧ y ∈ modularFunctionFieldQ M ∧
    y ^ 2 + cQ A.a₁ * x * y + cQ A.a₃ * y = x ^ 3 + cQ A.a₂ * x ^ 2 + cQ A.a₄ * x + cQ A.a₆ ∧
    ∃ n : ℤ, n ≠ 0 ∧ x.coeff n ≠ 0

/-- The denominator `2y + a₁x + a₃` of the invariant differential `ω_A = dx/(2y + a₁x + a₃)`. -/
def omegaDenom (A : WeierstrassCurve ℚ) (x y : LaurentSeries ℚ) : LaurentSeries ℚ :=
  2 * y + cQ A.a₁ * x + cQ A.a₃

/-- **The pull-back of `ω_A` is `c · g(q) dq/q`**: `θx = c · ĝ · (2y + a₁x + a₃)` in `ℂ((q))`,
where `ĝ` is the `q`-expansion of the cusp form `g`. Since `dq/q = 2πi dτ`, this says that the
pull-back of `ω_A` along the map `(x, y)` is `c · 2πi g(τ) dτ`. -/
def PullbackIsMultiple (A : WeierstrassCurve ℚ) (x y : LaurentSeries ℚ) (ĝ : PowerSeries ℂ)
    (c : ℂ) : Prop :=
  toComplexLaurent (eulerOp x) =
    HahnSeries.C c * (HahnSeries.ofPowerSeries ℤ ℂ ĝ * toComplexLaurent (omegaDenom A x y))

/-- A nonconstant `x` forces the scalar of the pull-back identity to be nonzero (PROVED). -/
theorem ne_zero_of_pullbackIsMultiple {A : WeierstrassCurve ℚ} {x y : LaurentSeries ℚ}
    {ĝ : PowerSeries ℂ} {c : ℂ} (hx : ∃ n : ℤ, n ≠ 0 ∧ x.coeff n ≠ 0)
    (h : PullbackIsMultiple A x y ĝ c) : c ≠ 0 := by
  rintro rfl
  obtain ⟨n, hn0, hxn⟩ := hx
  have h1 := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
  simp only [map_zero, zero_mul, HahnSeries.coeff_zero, toComplexLaurent_coeff,
    eulerOp_coeff] at h1
  have h2 : (n : ℚ) * x.coeff n = 0 := by exact_mod_cast h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hn0 (by exact_mod_cast h3)
  · exact hxn h3

/-- **Rationality of the pull-back scalar** (PROVED). If `x` is not constant and the `q`-expansion
`ĝ` has rational coefficients `b` with `b 1 = 1`, then a scalar `c` with
`PullbackIsMultiple A x y ĝ c` is rational. -/
theorem exists_rat_eq_of_pullbackIsMultiple {A : WeierstrassCurve ℚ} {x y : LaurentSeries ℚ}
    (hx : ∃ n : ℤ, n ≠ 0 ∧ x.coeff n ≠ 0) {b : ℕ → ℚ} (hb1 : b 1 = 1) {c : ℂ}
    (h : PullbackIsMultiple A x y ((PowerSeries.mk b).map (algebraMap ℚ ℂ)) c) :
    ∃ r : ℚ, (r : ℂ) = c := by
  set G : LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk b) with hG
  set u : LaurentSeries ℚ := G * omegaDenom A x y with hu
  have hmap : toComplexLaurent (eulerOp x) = HahnSeries.C c * toComplexLaurent u := by
    rw [h, hu, toComplexLaurent_mul, hG, toComplexLaurent_ofPowerSeries]
  have hG0 : G ≠ 0 := by
    intro hG0
    have h1 := congrArg (fun z : LaurentSeries ℚ => z.coeff 1) hG0
    simp only [hG, HahnSeries.coeff_zero] at h1
    have : (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk b)).coeff ((1 : ℕ) : ℤ) = b 1 := by
      rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]
    rw [show ((1 : ℕ) : ℤ) = 1 by rfl] at this
    rw [this, hb1] at h1
    exact one_ne_zero h1
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0, toComplexLaurent_zero, mul_zero] at hmap
    obtain ⟨n, hn0, hxn⟩ := hx
    have h1 := congrArg (fun z : LaurentSeries ℂ => z.coeff n) hmap
    simp only [toComplexLaurent_coeff, eulerOp_coeff, HahnSeries.coeff_zero] at h1
    have h2 : (n : ℚ) * x.coeff n = 0 := by exact_mod_cast h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hn0 (by exact_mod_cast h3)
    · exact hxn h3
  obtain ⟨n, hn⟩ : ∃ n : ℤ, u.coeff n ≠ 0 := by
    by_contra hcon
    apply hu0
    ext n
    by_contra hne
    exact hcon ⟨n, hne⟩
  refine ⟨(eulerOp x).coeff n / u.coeff n, ?_⟩
  have h1 := congrArg (fun z : LaurentSeries ℂ => z.coeff n) hmap
  simp only [toComplexLaurent_coeff, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
    smul_eq_mul] at h1
  have hun : ((u.coeff n : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Rat.cast_div, h1]
  field_simp

end ZInQ.Contrib.RC53Assist.NewformPeriods
