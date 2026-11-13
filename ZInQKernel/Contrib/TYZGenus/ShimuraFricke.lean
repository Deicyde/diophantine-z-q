import ZInQKernel.Contrib.TYZGenus.ShimuraThetaDup

/-!
# tyz-cm: the Fricke involution on x0-32's model (`X0.EtaModelFricke`, proved)

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

**Main result**: `etaModelFricke : X0.EtaModelFricke` (`φ(−1/(32τ)) + φ(τ) = T = (2, −4)`).

With `Q = e^{2πiτ}` and the theta constants `a = θ₀₀(16τ) = θ(0;16τ)`, `b = θ₁₀(16τ) = Q²θ(8τ;16τ)`,
`p = θ₀₀(8τ) = θ(0;8τ)`, `r = θ₁₀(8τ) = Qθ(4τ;8τ)`:
* `x = 2a/b`, `y = −2pr/b²` (`ShimuraThetaDup.lean`), and, from x0-32's eta forms of
  `x(−1/(32τ))`, `y(−1/(32τ))` (`X0.xC_fricke`, `X0.yC_fricke`) and the product forms,
  `x' = 2 + 4r/(p − r)`, `y' = −4(a² − b²)/(p − r)²` (`θ₀₁(2τ) = p − r` by a parity split,
  `θ₀₁(8τ)² = a² − b²` by a duplication formula);
* `p² = a² + b²`, `r² = 2ab` (duplication formulas);
* the chord construction of `T + (−P)`, `P = (x, y)`, gives `(x', y')`: two polynomial identities
  in the ideal `(p² − a² − b², r² − 2ab)` (cofactors computed with sympy,
  `scratch/tyz-cm/fricke_cof.py`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open Complex Filter Topology
open scoped Real
open ZInQ.GZTheta (gp gp_mul_gp gp_even_mul_odd gp_pow multipliable_geom_lin jtpA jtpA_ne_zero
  jtpA_eq_gp jtpB_eq_gp jtpP qJ eJ jacobiTheta₂_eq_jtpP jtpP_half_eq_gp)

variable {τ : ℂ}

/-! ## Two more theta identities -/

/-- **`θ(1/2;τ)² = θ(0;2τ)² − e^{πiτ}θ(τ;2τ)²`.** -/
theorem theta_dup_half_sign (hτ : 0 < τ.im) :
    jacobiTheta₂ (1 / 2) τ ^ 2 =
      jacobiTheta₂ 0 (2 * τ) ^ 2 - cexp (π * I * τ) * jacobiTheta₂ τ (2 * τ) ^ 2 := by
  have h2 : 0 < (2 * τ).im := by simp; linarith
  have hF := hasSum_theta_mul (z := 1 / 2) (w := 1 / 2) hτ hτ
  have h1 : HasSum
      ((fun p : ℤ × ℤ => jacobiTheta₂_term p.1 (1 / 2) τ * jacobiTheta₂_term p.2 (1 / 2) τ) ∘ evI)
      (jacobiTheta₂ 0 (2 * τ) * jacobiTheta₂ 0 (2 * τ)) := by
    refine (hasSum_theta_mul (z := 0) (w := 0) h2 h2).congr_fun fun p => ?_
    simp only [Function.comp_apply, evI, jacobiTheta₂_term, ← Complex.exp_add]
    have : 2 * (π : ℂ) * I * ((p.1 + p.2 : ℤ) : ℂ) * (1 / 2) + π * I * ((p.1 + p.2 : ℤ) : ℂ) ^ 2 * τ +
        (2 * π * I * ((p.1 - p.2 : ℤ) : ℂ) * (1 / 2) + π * I * ((p.1 - p.2 : ℤ) : ℂ) ^ 2 * τ) =
        (2 * π * I * (p.1 : ℂ) * 0 + π * I * (p.1 : ℂ) ^ 2 * (2 * τ) +
          (2 * π * I * (p.2 : ℂ) * 0 + π * I * (p.2 : ℂ) ^ 2 * (2 * τ))) + (p.1 : ℂ) * (2 * π * I) := by
      push_cast; ring
    rw [this, Complex.exp_add _ ((p.1 : ℂ) * (2 * π * I)), Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have h3 : HasSum
      ((fun p : ℤ × ℤ => jacobiTheta₂_term p.1 (1 / 2) τ * jacobiTheta₂_term p.2 (1 / 2) τ) ∘ odI)
      (-cexp (π * I * τ) * (jacobiTheta₂ τ (2 * τ) * jacobiTheta₂ τ (2 * τ))) := by
    refine ((hasSum_theta_mul (z := τ) (w := τ) h2 h2).mul_left (-cexp (π * I * τ))).congr_fun
      fun p => ?_
    simp only [Function.comp_apply, odI, jacobiTheta₂_term, ← Complex.exp_add]
    have : 2 * (π : ℂ) * I * ((p.1 + p.2 + 1 : ℤ) : ℂ) * (1 / 2) +
        π * I * ((p.1 + p.2 + 1 : ℤ) : ℂ) ^ 2 * τ +
        (2 * π * I * ((p.1 - p.2 : ℤ) : ℂ) * (1 / 2) + π * I * ((p.1 - p.2 : ℤ) : ℂ) ^ 2 * τ) =
        (π * I * τ + (2 * π * I * (p.1 : ℂ) * τ + π * I * (p.1 : ℂ) ^ 2 * (2 * τ) +
          (2 * π * I * (p.2 : ℂ) * τ + π * I * (p.2 : ℂ) ^ 2 * (2 * τ)))) +
          (π * I + (p.1 : ℂ) * (2 * π * I)) := by
      push_cast; ring
    rw [this, Complex.exp_add _ (π * I + (p.1 : ℂ) * (2 * π * I)), Complex.exp_add (π * I),
      Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
    rw [Complex.exp_add (π * I * τ)]
    ring
  have := eq_add_of_split hF h1 h3
  rw [sq, this]; ring

/-- **Parity split `θ(1/2;τ) = θ(0;4τ) − e^{πiτ}θ(2τ;4τ)`.** -/
theorem theta_parity_gen (hτ : 0 < τ.im) :
    jacobiTheta₂ (1 / 2) τ = jacobiTheta₂ 0 (4 * τ) - cexp (π * I * τ) * jacobiTheta₂ (2 * τ) (4 * τ) := by
  have h4 : 0 < (4 * τ).im := by simp; linarith
  set f : ℤ → ℂ := fun n => jacobiTheta₂_term n (1 / 2) τ with hfdef
  have hf : HasSum f (jacobiTheta₂ (1 / 2) τ) := hasSum_jacobiTheta₂_term _ hτ
  have he : HasSum (f ∘ fun m : ℤ => 2 * m) (jacobiTheta₂ 0 (4 * τ)) := by
    refine (hasSum_jacobiTheta₂_term 0 h4).congr_fun fun m => ?_
    simp only [Function.comp_apply, hfdef, jacobiTheta₂_term]
    have : 2 * (π : ℂ) * I * ((2 * m : ℤ) : ℂ) * (1 / 2) + π * I * ((2 * m : ℤ) : ℂ) ^ 2 * τ =
        (2 * π * I * (m : ℂ) * 0 + π * I * (m : ℂ) ^ 2 * (4 * τ)) + (m : ℂ) * (2 * π * I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have ho : HasSum (f ∘ fun m : ℤ => 2 * m + 1)
      (-cexp (π * I * τ) * jacobiTheta₂ (2 * τ) (4 * τ)) := by
    refine ((hasSum_jacobiTheta₂_term (2 * τ) h4).mul_left (-cexp (π * I * τ))).congr_fun
      fun m => ?_
    simp only [Function.comp_apply, hfdef, jacobiTheta₂_term]
    rw [neg_mul, ← Complex.exp_add]
    have : 2 * (π : ℂ) * I * ((2 * m + 1 : ℤ) : ℂ) * (1 / 2) +
        π * I * ((2 * m + 1 : ℤ) : ℂ) ^ 2 * τ =
        (π * I * τ + (2 * π * I * (m : ℂ) * (2 * τ) + π * I * (m : ℂ) ^ 2 * (4 * τ))) +
          (π * I + (m : ℂ) * (2 * π * I)) := by
      push_cast; ring
    rw [this, Complex.exp_add _ (π * I + (m : ℂ) * (2 * π * I)), Complex.exp_add (π * I),
      Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
    ring
  have hcompl : IsCompl (Set.range fun m : ℤ => 2 * m) (Set.range fun m : ℤ => 2 * m + 1) := by
    rw [isCompl_iff, disjoint_iff, codisjoint_iff]
    constructor
    · ext n
      simp only [Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_range, Set.bot_eq_empty,
        Set.mem_empty_iff_false, iff_false, not_and, forall_exists_index]
      rintro a rfl ⟨b, hb⟩
      omega
    · ext n
      simp only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Set.top_eq_univ, Set.mem_univ,
        iff_true]
      rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
      · exact Or.inl ⟨k, rfl⟩
      · exact Or.inr ⟨k, rfl⟩
  have he' := (Function.Injective.hasSum_range_iff (f := f)
    (g := fun m : ℤ => 2 * m) (fun a b h => by simpa using h)).mpr he
  have ho' := (Function.Injective.hasSum_range_iff (f := f)
    (g := fun m : ℤ => 2 * m + 1) (fun a b h => by simpa using h)).mpr ho
  have := HasSum.add_isCompl (f := f) hcompl he' ho'
  rw [hf.unique this]
  ring

/-! ## Product forms at `2τ` and `8τ` -/

theorem theta_half_two (hτ : 0 < τ.im) :
    jacobiTheta₂ (1 / 2) (2 * τ) = gp (Qt τ) (-1) 2 2 * gp (Qt τ) (-1) 2 1 ^ 2 := by
  have h2 : 0 < (2 * τ).im := by simp; linarith
  rw [jacobiTheta₂_eq_jtpP h2, jtpP_half_eq_gp,
    show (2 : ℂ) * τ = ((2 * 1 : ℕ) : ℂ) * τ by norm_num, qJ_mul_nat, pow_one]
  ring

theorem theta_half_eight (hτ : 0 < τ.im) :
    jacobiTheta₂ (1 / 2) (8 * τ) = gp (Qt τ) (-1) 8 8 * gp (Qt τ) (-1) 8 4 ^ 2 := by
  have h8 : 0 < (8 * τ).im := by simp; linarith
  rw [jacobiTheta₂_eq_jtpP h8, jtpP_half_eq_gp,
    show (8 : ℂ) * τ = ((2 * 4 : ℕ) : ℂ) * τ by norm_num, qJ_mul_nat, gp_pow, gp_pow]
  norm_num
  ring

theorem theta_four_eight (hτ : 0 < τ.im) :
    jacobiTheta₂ (4 * τ) (8 * τ) = 2 * gp (Qt τ) (-1) 8 8 * gp (Qt τ) 1 8 8 ^ 2 := by
  have := theta_k_2k hτ 4 (by norm_num)
  norm_num at this
  exact this

/-! ## The coordinates of `φ(−1/(32τ))` through theta values -/

theorem cexp_pi_two (τ : ℂ) : cexp (π * I * (2 * τ)) = Qt τ := by
  rw [Qt_def]; congr 1; ring

theorem cexp_pi_eight (τ : ℂ) : cexp (π * I * (8 * τ)) = Qt τ ^ 4 := by
  rw [Qt_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem xC_fricke_theta (τ : UpperHalfPlane) :
    X0.xC (-1 / (32 * (τ : ℂ))) = 2 + 4 * (Qt τ * jacobiTheta₂ (4 * τ) (8 * τ)) /
      (jacobiTheta₂ 0 (8 * τ) - Qt τ * jacobiTheta₂ (4 * τ) (8 * τ)) := by
  have hτ := τ.im_pos
  have hq := norm_Qt_lt_one hτ
  have h2 : 0 < (2 * (τ : ℂ)).im := by simp; linarith
  have hpar := theta_parity_gen h2
  rw [show 4 * (2 * (τ : ℂ)) = 8 * τ by ring, show 2 * (2 * (τ : ℂ)) = 4 * τ by ring,
    cexp_pi_two] at hpar
  rw [X0.xC_fricke, ← hpar, theta_half_two hτ, theta_four_eight hτ]
  have hG1 : gp (Qt τ) (-1) 1 1 = gp (Qt τ) (-1) 2 1 * gp (Qt τ) (-1) 2 2 := by
    have := gp_even_mul_odd hq (-1) 1 1 (by norm_num); norm_num at this; rw [← this]
  have hG16 : gp (Qt τ) (-1) 16 16 = gp (Qt τ) (-1) 8 8 * gp (Qt τ) 1 8 8 := by
    have := gp_mul_neg hq 8 8 (by norm_num); norm_num at this; rw [← this]
  simp only [X0.etaD]
  have e1 := eta_eq_gp 1 τ
  rw [Nat.cast_one, one_mul] at e1
  rw [show ((1 : ℕ) : ℂ) * (τ : ℂ) = τ by simp, e1, eta_eq_gp 2, eta_eq_gp 8, eta_eq_gp 16,
    hG1, hG16]
  have h24 : X0.wz (τ : ℂ) ^ 24 = Qt τ := by rw [X0.wz_pow_24, Qt_def]
  have hw := X0.wz_ne_zero (τ : ℂ)
  have hG2 := gp_A_ne_zero hτ 1 (by norm_num)
  have hG8 := gp_A_ne_zero hτ 4 (by norm_num)
  norm_num at hG2 hG8
  have hB1 : gp (Qt τ) (-1) 2 1 ≠ 0 := by
    intro h
    have := X0.etaD_ne_zero (d := 1) (by norm_num) τ
    simp only [X0.etaD, Nat.cast_one, one_mul] at this
    rw [e1, hG1, h] at this
    simp at this
  set w := X0.wz (τ : ℂ)
  set G21 := gp (Qt τ) (-1) 2 1
  set G2 := gp (Qt τ) (-1) 2 2
  set G8 := gp (Qt τ) (-1) 8 8
  set G188 := gp (Qt τ) 1 8 8
  rw [← h24]
  field_simp
  ring

theorem yC_fricke_theta (τ : UpperHalfPlane) :
    X0.yC (-1 / (32 * (τ : ℂ))) = -(4 * jacobiTheta₂ (1 / 2) (8 * τ) ^ 2 /
      (jacobiTheta₂ 0 (8 * τ) - Qt τ * jacobiTheta₂ (4 * τ) (8 * τ)) ^ 2) := by
  have hτ := τ.im_pos
  have hq := norm_Qt_lt_one hτ
  have h2 : 0 < (2 * (τ : ℂ)).im := by simp; linarith
  have hpar := theta_parity_gen h2
  rw [show 4 * (2 * (τ : ℂ)) = 8 * τ by ring, show 2 * (2 * (τ : ℂ)) = 4 * τ by ring,
    cexp_pi_two] at hpar
  rw [X0.yC_fricke, ← hpar, theta_half_two hτ, theta_half_eight hτ]
  have hG1 : gp (Qt τ) (-1) 1 1 = gp (Qt τ) (-1) 2 1 * gp (Qt τ) (-1) 2 2 := by
    have := gp_even_mul_odd hq (-1) 1 1 (by norm_num); norm_num at this; rw [← this]
  have hG4 : gp (Qt τ) (-1) 4 4 = gp (Qt τ) (-1) 8 4 * gp (Qt τ) (-1) 8 8 := by
    have := gp_even_mul_odd hq (-1) 4 4 (by norm_num); norm_num at this; rw [← this]
  simp only [X0.etaD]
  have e1 := eta_eq_gp 1 τ
  rw [Nat.cast_one, one_mul] at e1
  rw [show ((1 : ℕ) : ℂ) * (τ : ℂ) = τ by simp, e1, eta_eq_gp 2, eta_eq_gp 4, eta_eq_gp 8,
    hG1, hG4]
  have hw := X0.wz_ne_zero (τ : ℂ)
  have hG2 := gp_A_ne_zero hτ 1 (by norm_num)
  have hG8 := gp_A_ne_zero hτ 4 (by norm_num)
  norm_num at hG2 hG8
  have hB1 : gp (Qt τ) (-1) 2 1 ≠ 0 := by
    intro h
    have := X0.etaD_ne_zero (d := 1) (by norm_num) τ
    simp only [X0.etaD, Nat.cast_one, one_mul] at this
    rw [e1, hG1, h] at this
    simp at this
  set w := X0.wz (τ : ℂ)
  congr 1
  field_simp

/-! ## The chord identities -/

section Alg
variable {a b p r : ℂ}

theorem fricke_I1 (hp : p ^ 2 = a ^ 2 + b ^ 2) (hr : r ^ 2 = 2 * a * b) (hb : b ≠ 0)
    (hab : a - b ≠ 0) (hpr : p - r ≠ 0) :
    ((2 * b ^ 2 + p * r) / (b * (a - b))) ^ 2 - 2 - 2 * a / b = 2 + 4 * r / (p - r) := by
  rw [← sub_eq_zero]
  have key : ((2 * b ^ 2 + p * r) / (b * (a - b))) ^ 2 - 2 - 2 * a / b - (2 + 4 * r / (p - r)) =
      (-2*a^3*b*p + 2*a^3*b*r - 4*a^2*b^2*r + 6*a*b^3*p + 2*a*b^3*r - 4*b^4*r + 4*b^2*p^2*r
        - 4*b^2*p*r^2 + p^3*r^2 - p^2*r^3) / (b ^ 2 * (a - b) ^ 2 * (p - r)) := by
    field_simp
    ring
  rw [key, div_eq_zero_iff]
  left
  linear_combination (r * (4 * b ^ 2 + p * r - r ^ 2)) * hp +
    (a ^ 2 * p - a ^ 2 * r - 3 * b ^ 2 * p - b ^ 2 * r) * hr

theorem fricke_I2 (hp : p ^ 2 = a ^ 2 + b ^ 2) (hr : r ^ 2 = 2 * a * b) (hb : b ≠ 0)
    (hab : a - b ≠ 0) (hpr : p - r ≠ 0) :
    -((2 * b ^ 2 + p * r) / (b * (a - b)) * ((2 + 4 * r / (p - r)) - 2) - 4) =
      -(4 * (a ^ 2 - b ^ 2) / (p - r) ^ 2) := by
  rw [← sub_eq_zero]
  have key : -((2 * b ^ 2 + p * r) / (b * (a - b)) * ((2 + 4 * r / (p - r)) - 2) - 4) -
      -(4 * (a ^ 2 - b ^ 2) / (p - r) ^ 2) =
      (4*a^3*b - 4*a^2*b^2 - 4*a*b^3 + 4*a*b*p^2 - 8*a*b*p*r + 4*a*b*r^2 + 4*b^4 - 4*b^2*p^2
        + 4*b^2*r^2 - 4*p^2*r^2 + 4*p*r^3) / (b * (a - b) * (p - r) ^ 2) := by
    field_simp
    ring
  rw [key, div_eq_zero_iff]
  left
  linear_combination (-4 * (-a * b + b ^ 2 + r ^ 2)) * hp + (4 * (-a ^ 2 + a * b + p * r)) * hr

end Alg

/-! ## `X0.EtaModelFricke` -/

theorem curveAC_a₂ : X0.curveAC.a₂ = 0 := by
  simp [X0.curveAC, ZInQ.Contrib.TYZDecomp.CurveA.curveA, ZInQ.shortCurve,
    WeierstrassCurve.baseChange]

/-- **x0-32's leaf `X0.EtaModelFricke`, proved**: `φ(−1/(32τ)) + φ(τ) = T = (2, −4)`. -/
theorem etaModelFricke : X0.EtaModelFricke := by
  intro τ τ' hτ'
  have hτ := τ.im_pos
  have h4 : 0 < (4 * (τ : ℂ)).im := by simp; linarith
  have h8 : 0 < (8 * (τ : ℂ)).im := by simp; linarith
  obtain ⟨h, hP⟩ := X0.phiC_eq_some etaModelEquation τ
  obtain ⟨h', hP'⟩ := X0.phiC_eq_some etaModelEquation τ'
  have hQ := Qt_ne_zero (τ : ℂ)
  -- duplication formulas
  have d1a := theta_dup_half h8
  have d1b := theta_dup_half h4
  have d2 := theta_dup_zero h8
  have d3 := theta_dup_half_sign h8
  rw [show 8 * (τ : ℂ) / 2 = 4 * τ by ring, show 2 * (8 * (τ : ℂ)) = 16 * τ by ring] at d1a
  rw [show 4 * (τ : ℂ) / 2 = 2 * τ by ring, show 2 * (4 * (τ : ℂ)) = 8 * τ by ring] at d1b
  rw [show 2 * (8 * (τ : ℂ)) = 16 * τ by ring, cexp_pi_eight] at d2 d3
  have hT1 : jacobiTheta₂ (8 * (τ : ℂ)) (16 * τ) ≠ 0 := by
    rw [theta_eight_sixteen hτ]
    have heul := euler_BCD hτ
    have hA := gp_A_ne_zero hτ 8 (by norm_num)
    norm_num at hA
    have hB : gp (Qt τ) 1 16 16 ≠ 0 := fun h => by rw [h] at heul; simp at heul
    exact mul_ne_zero (mul_ne_zero two_ne_zero hA) (pow_ne_zero _ hB)
  have hx := xC_theta τ
  have hy := yC_theta τ
  have hx' := xC_fricke_theta τ
  have hy' := yC_fricke_theta τ
  rw [← hτ'] at hx' hy'
  have hx2 := xC_sub_two_ne_zero τ
  have hx2' := xC_sub_two_ne_zero τ'
  set a := jacobiTheta₂ 0 (16 * (τ : ℂ))
  set T1 := jacobiTheta₂ (8 * (τ : ℂ)) (16 * τ)
  set p := jacobiTheta₂ 0 (8 * (τ : ℂ))
  set S1 := jacobiTheta₂ (4 * (τ : ℂ)) (8 * τ)
  set R1 := jacobiTheta₂ (2 * (τ : ℂ)) (4 * τ)
  set U := jacobiTheta₂ (1 / 2) (8 * (τ : ℂ))
  set Q := Qt (τ : ℂ)
  set b := Q ^ 2 * T1 with hbdef
  set r := Q * S1 with hrdef
  have hb : b ≠ 0 := mul_ne_zero (pow_ne_zero _ hQ) hT1
  have hp : p ^ 2 = a ^ 2 + b ^ 2 := by rw [d2]; ring
  have hr : r ^ 2 = 2 * a * b := by rw [hrdef, hbdef, mul_pow, d1a]; ring
  have hxa : X0.xC τ = 2 * a / b := hx
  have hya : X0.yC τ = -(2 * p * r / b ^ 2) := by
    rw [hy, d1b, hbdef, hrdef]; field_simp
  have hab : a - b ≠ 0 := by
    intro h0
    apply hx2
    rw [hxa, show a = b by linear_combination h0, mul_div_assoc, div_self hb]; ring
  have hpr : p - r ≠ 0 := by
    intro h0
    apply hx2'
    rw [hx', h0, div_zero]; ring
  have hxa' : X0.xC τ' = 2 + 4 * r / (p - r) := hx'
  have hya' : X0.yC τ' = -(4 * (a ^ 2 - b ^ 2) / (p - r) ^ 2) := by
    rw [hy', d3, hbdef]; ring
  have key : X0.phiC τ' = X0.ptTC + -X0.phiC τ := by
    rw [hP, hP', WeierstrassCurve.Affine.Point.neg_some, X0.ptTC,
      WeierstrassCurve.Affine.Point.add_of_X_ne (fun h0 => hx2 (by rw [← h0]; ring))]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    have hne : (2 : ℂ) ≠ X0.xC τ := fun h0 => hx2 (by rw [← h0]; ring)
    rw [negY_AC, WeierstrassCurve.Affine.slope_of_X_ne hne]
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, negY_AC, curveAC_a₁, curveAC_a₂, zero_mul, add_zero,
      sub_zero]
    have hℓ : (-4 - -X0.yC τ) / (2 - X0.xC τ) = (2 * b ^ 2 + p * r) / (b * (a - b)) := by
      rw [hxa, hya]
      have : (2 : ℂ) - 2 * a / b = -(2 * (a - b) / b) := by field_simp; ring
      rw [this]
      field_simp
      ring
    rw [hℓ, hxa, hxa', hya', fricke_I1 hp hr hb hab hpr]
    refine ⟨rfl, ?_⟩
    linear_combination (-1 : ℂ) * fricke_I2 hp hr hb hab hpr
  rw [key, neg_add_cancel_right]

end ZInQ.Contrib.TYZGenus.Shimura
