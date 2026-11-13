import ZInQKernel.Contrib.TYZGenus.ShimuraTheta

/-!
# tyz-cm: theta duplication formulas and x0-32's curve equation `y² = x³ + 4x` (proved)

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

**Main result**: `etaModelEquation : X0.EtaModelEquation` (x0-32's leaf X0-EQ, proved).

* Duplication formulas for Mathlib's `jacobiTheta₂` (`Im τ > 0`):
  `θ(0;τ)² = θ(0;2τ)² + e^{πiτ}θ(τ;2τ)²` (`theta_dup_zero`) and
  `θ(τ/2;τ)² = 2θ(0;2τ)θ(τ;2τ)` (`theta_dup_half`): the double series `Σ_{m,n}` is split along
  `(m, n) = (s + t, s − t)` and `(m, n) = (s + t + 1, s − t)`.
* With `Q = e^{2πiτ}`, `T₀ = θ(0;16τ)`, `T₁ = θ(8τ;16τ)`, `R₁ = θ(2τ;4τ)`:
  `x = 2T₀/(Q²T₁)` (`xC_theta`) and `y = −R₁²/(Q³T₁²)` (`yC_theta`), from the product forms
  (gz-theta's triple product) and Euler's identity; then
  `R₁⁴ = 8T₀T₁(T₀² + Q⁴T₁²)` by the duplication formulas at `4τ` and `8τ`, which is
  `y² = x³ + 4x`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open Complex Filter Topology
open scoped Real
open ZInQ.GZTheta (gp gp_mul_gp gp_even_mul_odd gp_pow multipliable_geom_lin jtpA jtpA_ne_zero
  jtpA_eq_gp jtpB_eq_gp jtpP qJ eJ jacobiTheta₂_eq_jtpP)

variable {τ : ℂ}

/-! ## Products of theta series and the parity split of `ℤ²` -/

theorem summable_norm_theta_term (z : ℂ) (hτ : 0 < τ.im) :
    Summable fun n : ℤ => ‖jacobiTheta₂_term n z τ‖ := by
  refine (summable_pow_mul_jacobiTheta₂_term_bound |z.im| hτ 0).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun n => ?_
  simpa only [pow_zero, one_mul] using norm_jacobiTheta₂_term_le hτ le_rfl le_rfl n

theorem hasSum_theta_mul {z w τ' : ℂ} (hτ : 0 < τ.im) (hτ' : 0 < τ'.im) :
    HasSum (fun p : ℤ × ℤ => jacobiTheta₂_term p.1 z τ * jacobiTheta₂_term p.2 w τ')
      (jacobiTheta₂ z τ * jacobiTheta₂ w τ') :=
  HasSum.mul (f := fun n : ℤ => jacobiTheta₂_term n z τ) (g := fun n : ℤ => jacobiTheta₂_term n w τ')
    (hasSum_jacobiTheta₂_term z hτ) (hasSum_jacobiTheta₂_term w hτ')
    (summable_mul_of_summable_norm (f := fun n : ℤ => jacobiTheta₂_term n z τ)
      (g := fun n : ℤ => jacobiTheta₂_term n w τ')
      (summable_norm_theta_term z hτ) (summable_norm_theta_term w hτ'))

/-- `(s, t) ↦ (s + t, s − t)`. -/
def evI (p : ℤ × ℤ) : ℤ × ℤ := (p.1 + p.2, p.1 - p.2)

/-- `(s, t) ↦ (s + t + 1, s − t)`. -/
def odI (p : ℤ × ℤ) : ℤ × ℤ := (p.1 + p.2 + 1, p.1 - p.2)

theorem evI_injective : Function.Injective evI := by
  intro p q h
  simp only [evI, Prod.mk.injEq] at h
  ext <;> omega

theorem odI_injective : Function.Injective odI := by
  intro p q h
  simp only [odI, Prod.mk.injEq] at h
  ext <;> omega

theorem isCompl_evI_odI : IsCompl (Set.range evI) (Set.range odI) := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  constructor
  · ext p
    simp only [Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_range, Set.bot_eq_empty,
      Set.mem_empty_iff_false, iff_false, not_and, forall_exists_index]
    rintro a rfl ⟨b, hb⟩
    simp only [evI, odI, Prod.mk.injEq] at hb
    omega
  · ext p
    simp only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Set.top_eq_univ, Set.mem_univ,
      iff_true]
    obtain ⟨m, n⟩ := p
    rcases Int.emod_two_eq_zero_or_one (m + n) with h | h
    · left
      exact ⟨((m + n) / 2, (m - n) / 2), by simp only [evI, Prod.mk.injEq]; omega⟩
    · right
      exact ⟨((m + n - 1) / 2, (m - n - 1) / 2), by simp only [odI, Prod.mk.injEq]; omega⟩

theorem eq_add_of_split {F : ℤ × ℤ → ℂ} {a b c : ℂ} (hF : HasSum F a) (h1 : HasSum (F ∘ evI) b)
    (h2 : HasSum (F ∘ odI) c) : a = b + c := by
  have h1' := (Function.Injective.hasSum_range_iff (f := F) evI_injective).mpr h1
  have h2' := (Function.Injective.hasSum_range_iff (f := F) odI_injective).mpr h2
  exact hF.unique (HasSum.add_isCompl isCompl_evI_odI h1' h2')

/-! ## The duplication formulas -/

/-- **`θ(0;τ)² = θ(0;2τ)² + e^{πiτ}θ(τ;2τ)²`.** -/
theorem theta_dup_zero (hτ : 0 < τ.im) :
    jacobiTheta₂ 0 τ ^ 2 = jacobiTheta₂ 0 (2 * τ) ^ 2 + cexp (π * I * τ) * jacobiTheta₂ τ (2 * τ) ^ 2 := by
  have h2 : 0 < (2 * τ).im := by simp; linarith
  have hF := hasSum_theta_mul (z := 0) (w := 0) hτ hτ
  have h1 : HasSum ((fun p : ℤ × ℤ => jacobiTheta₂_term p.1 0 τ * jacobiTheta₂_term p.2 0 τ) ∘ evI)
      (jacobiTheta₂ 0 (2 * τ) * jacobiTheta₂ 0 (2 * τ)) := by
    refine (hasSum_theta_mul (z := 0) (w := 0) h2 h2).congr_fun fun p => ?_
    simp only [Function.comp_apply, evI, jacobiTheta₂_term, ← Complex.exp_add]
    congr 1; push_cast; ring
  have h3 : HasSum ((fun p : ℤ × ℤ => jacobiTheta₂_term p.1 0 τ * jacobiTheta₂_term p.2 0 τ) ∘ odI)
      (cexp (π * I * τ) * (jacobiTheta₂ τ (2 * τ) * jacobiTheta₂ τ (2 * τ))) := by
    refine ((hasSum_theta_mul (z := τ) (w := τ) h2 h2).mul_left (cexp (π * I * τ))).congr_fun
      fun p => ?_
    simp only [Function.comp_apply, odI, jacobiTheta₂_term, ← Complex.exp_add]
    congr 1; push_cast; ring
  have := eq_add_of_split hF h1 h3
  rw [sq, sq, sq, this]

/-- **`θ(τ/2;τ)² = 2θ(0;2τ)θ(τ;2τ)`.** -/
theorem theta_dup_half (hτ : 0 < τ.im) :
    jacobiTheta₂ (τ / 2) τ ^ 2 = 2 * jacobiTheta₂ 0 (2 * τ) * jacobiTheta₂ τ (2 * τ) := by
  have h2 : 0 < (2 * τ).im := by simp; linarith
  have hF := hasSum_theta_mul (z := τ / 2) (w := τ / 2) hτ hτ
  have h1 : HasSum
      ((fun p : ℤ × ℤ => jacobiTheta₂_term p.1 (τ / 2) τ * jacobiTheta₂_term p.2 (τ / 2) τ) ∘ evI)
      (jacobiTheta₂ τ (2 * τ) * jacobiTheta₂ 0 (2 * τ)) := by
    refine (hasSum_theta_mul (z := τ) (w := 0) h2 h2).congr_fun fun p => ?_
    simp only [Function.comp_apply, evI, jacobiTheta₂_term, ← Complex.exp_add]
    congr 1; push_cast; ring
  have h3 : HasSum
      ((fun p : ℤ × ℤ => jacobiTheta₂_term p.1 (τ / 2) τ * jacobiTheta₂_term p.2 (τ / 2) τ) ∘ odI)
      (jacobiTheta₂ 0 (2 * τ) * jacobiTheta₂ τ (2 * τ)) := by
    have hp := hasSum_theta_mul (z := 0) (w := τ) h2 h2
    let e : ℤ × ℤ ≃ ℤ × ℤ := (Equiv.addRight (1 : ℤ)).prodCongr (Equiv.refl ℤ)
    rw [← e.hasSum_iff] at hp
    refine hp.congr_fun fun p => ?_
    simp only [Function.comp_apply, odI, e, Equiv.prodCongr_apply, Equiv.coe_addRight,
      Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id, jacobiTheta₂_term, ← Complex.exp_add]
    congr 1; push_cast; ring
  have := eq_add_of_split hF h1 h3
  rw [sq, this]; ring

/-! ## `x` and `y` through theta values -/

/-- `θ(kτ; 2kτ) = 2·∏(1 − Q^{2kn+2k})·∏(1 + Q^{2kn+2k})²`. -/
theorem theta_k_2k (hτ : 0 < τ.im) (k : ℕ) (hk : 0 < k) :
    jacobiTheta₂ ((k : ℂ) * τ) ((2 * k : ℕ) * τ) =
      2 * gp (Qt τ) (-1) (2 * k) (2 * k) * gp (Qt τ) 1 (2 * k) (2 * k) ^ 2 := by
  have h2k : 0 < (((2 * k : ℕ) : ℂ) * τ).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    have : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
    positivity
  have hq := norm_Qt_lt_one hτ
  have hQ := Qt_ne_zero τ
  rw [jacobiTheta₂_eq_jtpP h2k]
  unfold jtpP
  rw [jtpA_eq_gp, jtpB_eq_gp, jtpB_eq_gp, qJ_mul_nat,
    show -((k : ℂ) * τ) = -(((k : ℕ) : ℂ) * τ) by norm_num, ZInQ.GZTheta.eJ_neg, eJ_mul_nat,
    gp_pow, gp_pow, gp_pow]
  have hB : gp (Qt τ) (Qt τ ^ k) (k * 2) (k * 1) = gp (Qt τ) 1 (2 * k) (2 * k) := by
    unfold gp
    exact tprod_congr fun n => by ring
  have hB' : gp (Qt τ) (Qt τ ^ k)⁻¹ (k * 2) (k * 1) = 2 * gp (Qt τ) 1 (2 * k) (2 * k) := by
    have e1 : gp (Qt τ) (Qt τ ^ k)⁻¹ (k * 2) (k * 1) = gp (Qt τ) 1 (2 * k) 0 := by
      unfold gp
      refine tprod_congr fun n => ?_
      have : (Qt τ ^ k)⁻¹ * Qt τ ^ (k * 2 * n + k * 1) = Qt τ ^ (2 * k * n + 0) := by
        rw [show k * 2 * n + k * 1 = k + 2 * k * n by ring, pow_add, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero _ hQ), one_mul, add_zero]
      rw [this, one_mul]
    rw [e1]
    have hm1 : Multipliable (fun n : ℕ => 1 + 1 * Qt τ ^ (2 * k * (n + 1) + 0)) :=
      (multipliable_geom_lin hq 1 (2 * k) (2 * k) (by omega)).congr fun n => by ring_nf
    have h := tprod_eq_zero_mul' (f := fun n : ℕ => 1 + 1 * Qt τ ^ (2 * k * n + 0)) hm1
    beta_reduce at h
    unfold gp
    rw [h]
    congr 1
    rw [mul_zero, add_zero, pow_zero, mul_one]; norm_num
  rw [hB, hB']
  ring

theorem gp_A_ne_zero (hτ : 0 < τ.im) (k : ℕ) (hk : 0 < k) : gp (Qt τ) (-1) (2 * k) (2 * k) ≠ 0 := by
  have h2k : 0 < (((2 * k : ℕ) : ℂ) * τ).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    have : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
    positivity
  have := jtpA_ne_zero h2k
  rw [jtpA_eq_gp, qJ_mul_nat, gp_pow] at this
  rwa [show k * 2 = 2 * k by ring] at this

theorem xC_theta (τ : UpperHalfPlane) :
    X0.xC τ = 2 * jacobiTheta₂ 0 (16 * τ) /
      (Qt τ ^ 2 * jacobiTheta₂ (8 * τ) (16 * τ)) := by
  have hτ := τ.im_pos
  have hq := norm_Qt_lt_one hτ
  have hQ := Qt_ne_zero (τ : ℂ)
  have hG8 : gp (Qt τ) (-1) 8 8 = gp (Qt τ) (-1) 16 8 * gp (Qt τ) (-1) 16 16 := by
    have := gp_even_mul_odd hq (-1) 8 8 (by norm_num); norm_num at this; rw [← this]
  have hG32 : gp (Qt τ) (-1) 32 32 = gp (Qt τ) (-1) 16 16 * gp (Qt τ) 1 16 16 := by
    have := gp_mul_neg hq 16 16 (by norm_num); norm_num at this; rw [← this]
  have heul := euler_BCD hτ
  have hA := gp_A_ne_zero hτ 8 (by norm_num)
  norm_num at hA
  have hB : gp (Qt τ) 1 16 16 ≠ 0 := fun h => by rw [h] at heul; simp at heul
  rw [xC_eq_even, theta00_sixteen hτ, theta_eight_sixteen hτ]
  simp only [X0.etaD]
  rw [eta_eq_gp 8, eta_eq_gp 16, eta_eq_gp 32, hG8, hG32]
  have h48 := wz_pow_48 (τ : ℂ)
  have hw := X0.wz_ne_zero (τ : ℂ)
  set w := X0.wz (τ : ℂ)
  set A := gp (Qt τ) (-1) 16 16
  set B := gp (Qt τ) 1 16 16
  set C := gp (Qt τ) 1 16 8
  set D := gp (Qt τ) (-1) 16 8
  have hD : D ≠ 0 := fun h => by rw [h] at heul; simp at heul
  rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hw) (mul_ne_zero hD hA)))
    (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hw) (mul_ne_zero hA hB))))
    (mul_ne_zero (pow_ne_zero _ hQ) (mul_ne_zero (mul_ne_zero two_ne_zero hA) (pow_ne_zero _ hB)))]
  linear_combination (-2 * w ^ 96 * A ^ 7 * B ^ 2) * h48 +
    (-2 * w ^ 96 * A ^ 7 * B ^ 2 * w ^ 48 * (B * C * D + 1)) * heul

theorem theta_two_four (hτ : 0 < τ.im) :
    jacobiTheta₂ (2 * τ) (4 * τ) = 2 * gp (Qt τ) (-1) 4 4 * gp (Qt τ) 1 4 4 ^ 2 := by
  have := theta_k_2k hτ 2 (by norm_num)
  norm_num at this
  exact this

theorem yC_theta (τ : UpperHalfPlane) :
    X0.yC τ = -(jacobiTheta₂ (2 * τ) (4 * τ) ^ 2 /
      (Qt τ ^ 3 * jacobiTheta₂ (8 * τ) (16 * τ) ^ 2)) := by
  have hτ := τ.im_pos
  have hq := norm_Qt_lt_one hτ
  have hQ := Qt_ne_zero (τ : ℂ)
  have hG8 : gp (Qt τ) (-1) 8 8 = gp (Qt τ) (-1) 16 8 * gp (Qt τ) (-1) 16 16 := by
    have := gp_even_mul_odd hq (-1) 8 8 (by norm_num); norm_num at this; rw [← this]
  have hG32 : gp (Qt τ) (-1) 32 32 = gp (Qt τ) (-1) 16 16 * gp (Qt τ) 1 16 16 := by
    have := gp_mul_neg hq 16 16 (by norm_num); norm_num at this; rw [← this]
  have hGG : gp (Qt τ) (-1) 4 4 * gp (Qt τ) 1 4 4 = gp (Qt τ) (-1) 16 8 * gp (Qt τ) (-1) 16 16 := by
    rw [← hG8]; have := gp_mul_neg hq 4 4 (by norm_num); norm_num at this; exact this
  have heul := euler_BCD hτ
  have hA := gp_A_ne_zero hτ 8 (by norm_num)
  norm_num at hA
  have hB : gp (Qt τ) 1 16 16 ≠ 0 := fun h => by rw [h] at heul; simp at heul
  have hG4 := gp_A_ne_zero hτ 2 (by norm_num)
  norm_num at hG4
  unfold X0.yC
  rw [theta_two_four hτ, theta_eight_sixteen hτ]
  simp only [X0.etaD]
  rw [eta_eq_gp 4, eta_eq_gp 8, eta_eq_gp 16, eta_eq_gp 32, hG8, hG32]
  have h72 : X0.wz (τ : ℂ) ^ 72 = Qt τ ^ 3 := by
    rw [show 72 = 24 * 3 by norm_num, pow_mul, X0.wz_pow_24, Qt_def]
  have hw := X0.wz_ne_zero (τ : ℂ)
  set w := X0.wz (τ : ℂ)
  set A := gp (Qt τ) (-1) 16 16
  set B := gp (Qt τ) 1 16 16
  set D := gp (Qt τ) (-1) 16 8
  set G4 := gp (Qt τ) (-1) 4 4
  set G144 := gp (Qt τ) 1 4 4
  congr 1
  rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hw) hG4))
    (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hw) (mul_ne_zero hA hB))))
    (mul_ne_zero (pow_ne_zero _ hQ) (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hA)
      (pow_ne_zero _ hB))))]
  linear_combination (-4 * A ^ 8 * B ^ 4 * D ^ 4 * w ^ 64) * h72 +
    (-4 * w ^ 136 * A ^ 4 * B ^ 4 * ((G4 * G144) ^ 3 + (G4 * G144) ^ 2 * (D * A) +
      (G4 * G144) * (D * A) ^ 2 + (D * A) ^ 3)) * hGG

/-- **x0-32's leaf `X0.EtaModelEquation` (`y² = x³ + 4x` on `ℍ`), proved.** -/
theorem etaModelEquation : X0.EtaModelEquation := by
  intro τ
  have hτ := τ.im_pos
  have h4 : 0 < (4 * (τ : ℂ)).im := by simp; linarith
  have h8 : 0 < (8 * (τ : ℂ)).im := by simp; linarith
  have hQ := Qt_ne_zero (τ : ℂ)
  have hT1 : jacobiTheta₂ (8 * (τ : ℂ)) (16 * τ) ≠ 0 := by
    rw [theta_eight_sixteen hτ]
    have heul := euler_BCD hτ
    have hA := gp_A_ne_zero hτ 8 (by norm_num)
    norm_num at hA
    have hB : gp (Qt τ) 1 16 16 ≠ 0 := fun h => by rw [h] at heul; simp at heul
    exact mul_ne_zero (mul_ne_zero two_ne_zero hA) (pow_ne_zero _ hB)
  have d1a := theta_dup_half h8
  have d1b := theta_dup_half h4
  have d2 := theta_dup_zero h8
  rw [show 8 * (τ : ℂ) / 2 = 4 * τ by ring, show 2 * (8 * (τ : ℂ)) = 16 * τ by ring] at d1a
  rw [show 4 * (τ : ℂ) / 2 = 2 * τ by ring, show 2 * (4 * (τ : ℂ)) = 8 * τ by ring] at d1b
  rw [show 2 * (8 * (τ : ℂ)) = 16 * τ by ring,
    show cexp (π * I * (8 * (τ : ℂ))) = Qt τ ^ 4 by
      rw [Qt_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring] at d2
  rw [yC_theta, xC_theta]
  set T0 := jacobiTheta₂ 0 (16 * (τ : ℂ))
  set T1 := jacobiTheta₂ (8 * (τ : ℂ)) (16 * τ)
  set S0 := jacobiTheta₂ 0 (8 * (τ : ℂ))
  set S1 := jacobiTheta₂ (4 * (τ : ℂ)) (8 * τ)
  set R1 := jacobiTheta₂ (2 * (τ : ℂ)) (4 * τ)
  set Q := Qt (τ : ℂ)
  have hR4 : R1 ^ 4 = 8 * T0 * T1 * (T0 ^ 2 + Q ^ 4 * T1 ^ 2) := by
    linear_combination (R1 ^ 2 + 2 * S0 * S1) * d1b + 4 * S1 ^ 2 * d2 +
      4 * (T0 ^ 2 + Q ^ 4 * T1 ^ 2) * d1a
  have e1 : (-(R1 ^ 2 / (Q ^ 3 * T1 ^ 2))) ^ 2 = R1 ^ 4 / (Q ^ 6 * T1 ^ 4) := by
    field_simp
  have e2 : (2 * T0 / (Q ^ 2 * T1)) ^ 3 + 4 * (2 * T0 / (Q ^ 2 * T1)) =
      8 * T0 * T1 * (T0 ^ 2 + Q ^ 4 * T1 ^ 2) / (Q ^ 6 * T1 ^ 4) := by
    field_simp
    ring
  rw [e1, e2, hR4]

end ZInQ.Contrib.TYZGenus.Shimura
