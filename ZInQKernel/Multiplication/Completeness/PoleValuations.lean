import ZInQKernel.Multiplication.Completeness.PoleValuationsAux

/-!
# Valuations of the pole input of a completed slope

Blueprint: `multiplication/completeness/pole-input-valuations.md`.

For a good slope `t`, a sign `η`, a parameter `q` that is small at `S_b` and integral at the odd
contact primes of `t` outside `S_b`, and test values `D_{gj}` integral above `S_b` and precise at
one place above each selected prime, the pole input `B = R/Θ²` has `v_p(B) ≥ 103 C_p + 8` on
`S_b`, `v_p(B) = 1` at the selected primes, and even valuation elsewhere. Hence `v_p(B) ≥ 4` on
`S₀` and the reduced denominator of `B` is a square.

The article's statement is for `ℓ = ℓ₀`; here `ℓ` is any rational with the valuations of `ℓ₀`
(`v_p(ℓ) = E_p` on `S_b` and `0` elsewhere), which is all the proof uses.
-/

namespace ZInQ.Mult

open scoped BigOperators

/-- The pole input `B = R/Θ²` of the slope predicate, for given `ℓ, η, q, t` and test values
`D_{gj}`. -/
noncomputable def poleInput (ℓ η q t : ℚ) (D : Fin 6 → Fin 12 → K0) : ℚ :=
  slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t) /
    traceTheta (fun g => groupW (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t))
      (normTests (slopeR0 η t) t (D g))) ^ 2

theorem prec_cases (j : Fin 12) : prec j = 1 ∨ prec j = 25 := by
  unfold prec; split_ifs <;> simp

/-- The valuation of a normalized test value at a prime `ρ` where rationals have valuation
`e v_p`. -/
theorem vge_normTests {p : ℕ} [Fact p.Prime] {ρ : Zs} (hρ : Prime ρ) {e : ℤ}
    (hev : ∀ r : ℚ, r ≠ 0 → vP ρ hρ (r : K0) = ((e * padicValRat p r : ℤ) : WithTop ℤ))
    {R0 t : ℚ} (hR0 : R0 ≠ 0) (ht1 : t ≠ 1) {D : Fin 12 → K0} {j : Fin 12} {m : ℤ}
    (hD : Vge (vP ρ hρ) m (D j)) :
    Vge (vP ρ hρ) (m - e * (prec j * padicValRat p R0 + (prec j + 1) * padicValRat p (t - 1)))
      (normTests R0 t D j) := by
  have hden : ((R0 : K0) ^ prec j * ((t - 1 : ℚ) : K0) ^ (prec j + 1)) =
      ((R0 ^ prec j * (t - 1) ^ (prec j + 1) : ℚ) : K0) := by push_cast; ring
  have hne : R0 ^ prec j * (t - 1) ^ (prec j + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hR0) (pow_ne_zero _ (sub_ne_zero.mpr ht1))
  have hv : vP ρ hρ ((R0 : K0) ^ prec j * ((t - 1 : ℚ) : K0) ^ (prec j + 1)) =
      ((e * (prec j * padicValRat p R0 + (prec j + 1) * padicValRat p (t - 1)) : ℤ) :
        WithTop ℤ) := by
    rw [hden, hev _ hne]
    rw [padicValRat.mul (pow_ne_zero _ hR0) (pow_ne_zero _ (sub_ne_zero.mpr ht1)),
      padicValRat.pow, padicValRat.pow]
    push_cast; ring_nf
  exact hD.div_val' hv

/-- `v(R C²) ≥ e v_p(R) + 2 (m - e X)` for `C` as in `vge_normTests`. -/
theorem vge_R_mul_sq {p : ℕ} {ρ : Zs} (hρ : Prime ρ) {e : ℤ}
    (hev : ∀ r : ℚ, r ≠ 0 → vP ρ hρ (r : K0) = ((e * padicValRat p r : ℤ) : WithTop ℤ))
    {R : ℚ} (hR : R ≠ 0) {C : K0} {n : ℤ} (hC : Vge (vP ρ hρ) n C) :
    Vge (vP ρ hρ) (e * padicValRat p R + 2 * n) ((R : K0) * C ^ 2) := by
  have := (Vge.of_eq (hev R hR)).mul (hC.pow 2)
  exact this.mono (by push_cast; linarith)

/-- **Valuations of the pole input of a completed slope.** -/
theorem pole_input_valuations {B₀ : ℝ} {t : ℚ} (ht : GoodSlope B₀ t) {η q ℓ : ℚ}
    (hη : η = 1 ∨ η = -1) (hℓ0 : ℓ ≠ 0)
    (hℓ : ∀ p : ℕ, p.Prime → padicValRat p ℓ = if p ∈ S_b then (Ep p : ℤ) else 0)
    (hq_old : ∀ p ∈ S_b, (Cp p : ℤ) ≤ padicValRat p q)
    (hq_sel : ∀ p : ℕ, p ∉ S_b → IsOddContactPrime t p → 0 ≤ padicValRat p q)
    (ha : slopeA (slopeR0 η t) q ≠ 0) (D : Fin 6 → Fin 12 → K0)
    (hD_old : ∀ p ∈ S_b, ∀ (π : Zs) (hπ : Prime π), π ∣ (p : Zs) →
      ∀ g j, Vge (vP π hπ) 0 (D g j))
    (hD_sel : ∀ p : ℕ, p ∉ S_b → IsOddContactPrime t p →
      ∃ g, ∃ (π : Zs) (hπ : Prime π), π ∣ (p : Zs) ∧ ∀ j, Vge (vP π hπ) (prec j) (D g j))
    (hW : ∀ g, groupW (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t))
      (normTests (slopeR0 η t) t (D g)) ≠ 0)
    (hΘ : traceTheta (fun g => groupW (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t))
      (normTests (slopeR0 η t) t (D g))) ≠ 0) :
    (∀ p ∈ S_b, ((103 * Cp p + 8 : ℕ) : ℤ) ≤ padicValRat p (poleInput ℓ η q t D)) ∧
    (∀ p : ℕ, p ∉ S_b → IsOddContactPrime t p → padicValRat p (poleInput ℓ η q t D) = 1) ∧
    (∀ p : ℕ, p.Prime → p ∉ S_b → ¬ IsOddContactPrime t p →
      Even (padicValRat p (poleInput ℓ η q t D))) ∧
    (∀ p ∈ poleS0, 4 ≤ padicValRat p (poleInput ℓ η q t D)) ∧
    IsSquare (poleInput ℓ η q t D).den := by
  classical
  set R0 := slopeR0 η t with hR0def
  set a := slopeA R0 q with hadef
  set R := slopeR ℓ a R0 with hRdef
  set C : Fin 6 → Fin 12 → K0 := fun g => normTests R0 t (D g) with hCdef
  set W : Fin 6 → K0 := fun g => groupW R (C g) with hWdef
  set Θ := traceTheta W with hΘdef
  have hB : poleInput ℓ η q t D = R / Θ ^ 2 := rfl
  have hR0 : R0 ≠ 0 := slopeR0_ne_zero hη ht.not_mem_contactSet ht.ne_one
  have hR : R ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hℓ0) (pow_ne_zero _ ha)) hR0
  have ht1 := ht.ne_one
  -- the rational valuations of `B`, `R` and `R₀`
  have hvB : ∀ p : ℕ, p.Prime → padicValRat p (R / Θ ^ 2) =
      2 * padicValRat p ℓ + 2 * padicValRat p a + padicValRat p R0 - 2 * padicValRat p Θ := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    rw [padicValRat.div hR (pow_ne_zero _ hΘ), padicValRat.pow, hRdef, slopeR,
      padicValRat.mul (mul_ne_zero (pow_ne_zero _ hℓ0) (pow_ne_zero _ ha)) hR0,
      padicValRat.mul (pow_ne_zero _ hℓ0) (pow_ne_zero _ ha), padicValRat.pow, padicValRat.pow]
    push_cast; ring
  have hvR : ∀ p : ℕ, p.Prime → padicValRat p R =
      2 * padicValRat p ℓ + 2 * padicValRat p a + padicValRat p R0 := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    rw [hRdef, slopeR, padicValRat.mul (mul_ne_zero (pow_ne_zero _ hℓ0) (pow_ne_zero _ ha)) hR0,
      padicValRat.mul (pow_ne_zero _ hℓ0) (pow_ne_zero _ ha), padicValRat.pow, padicValRat.pow]
    push_cast; ring
  have hvR0 : ∀ p : ℕ, p.Prime →
      padicValRat p R0 = padicValRat p (contactPoly t / (t - 1) ^ 8) := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    have hη0 : η ≠ 0 := by rcases hη with rfl | rfl <;> norm_num
    rw [hR0def, slopeR0, mul_div_assoc, padicValRat.mul hη0 (div_ne_zero
      (contactPoly_ne_zero ht.not_mem_contactSet) (pow_ne_zero _ (sub_ne_zero.mpr ht1))),
      padicValRat_eta hη, zero_add]
  -- `Θ` and `R` in `K₀`
  have hΘK : ((Θ : ℚ) : K0) = (∑ g, (W g)⁻¹) + star (∑ g, (W g)⁻¹) := by
    rw [hΘdef, traceTheta, trace_cast_K0]
  ------------------------------------------------------------------
  -- Part 1: the old primes
  have part1 : ∀ p ∈ S_b, ((103 * Cp p + 8 : ℕ) : ℤ) ≤ padicValRat p (R / Θ ^ 2) := by
    intro p hpS
    have hp := prime_of_mem_S_b hpS
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨hold1, hold2⟩ := ht.old p hpS
    have hq0 : q ≠ 0 := by
      rintro rfl
      have := hq_old p hpS
      simp only [padicValRat.zero] at this
      have : (14 : ℤ) ≤ Cp p := by unfold Cp; have := Nat.zero_lt_of_ne_zero (show Bp p ≠ 0 by
        unfold Bp; split_ifs <;> norm_num); push_cast; omega
      omega
    have hBp : (1 : ℤ) ≤ Bp p := by unfold Bp; split_ifs <;> norm_num
    have hCp : (Cp p : ℤ) = 14 * Bp p := by unfold Cp; push_cast; ring
    have hEp : (Ep p : ℤ) = 52 * Cp p + padicValNat p 12 + 4 := by unfold Ep; push_cast; ring
    -- `a` is a `p`-adic unit
    have hva : padicValRat p a = 0 := by
      apply padicValRat_one_sub
      right
      rw [padicValRat.mul hR0 (pow_ne_zero _ hq0), padicValRat.pow, hvR0 p hp]
      have := hq_old p hpS
      rw [abs_le] at hold2
      push_cast at this ⊢
      linarith [hold2.1]
    have hvl := hℓ p hp
    simp only [hpS, ↓reduceIte] at hvl
    -- `v_p(R) = 2 E_p + v_p(R₀)`
    have hvR' : padicValRat p R = 2 * Ep p + padicValRat p R0 := by
      rw [hvR p hp, hvl, hva]; ring
    -- valuations above `p`
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨π, hπ, hπp⟩ := exists_prime_dvd_natCast p
    obtain ⟨e, he1, hev⟩ := exists_vP_ratCast hp hπ hπp
    have hev' : ∀ r : ℚ, r ≠ 0 →
        vP (star π) (prime_star hπ) (r : K0) = ((e * padicValRat p r : ℤ) : WithTop ℤ) := by
      intro r hr; rw [vP_star hπ, star_ratCast, hev r hr]
    set v12 : ℤ := ((padicValNat p 12 : ℕ) : ℤ) with hv12
    set m : ℤ := e * v12 + 1 with hm
    have hm1 : 1 ≤ m := by
      have : 0 ≤ v12 := Int.natCast_nonneg _
      nlinarith
    -- at each prime `ρ ∈ {π, σπ}`, `v(W_g⁻¹ - 1) ≥ m`
    have hWρ : ∀ (ρ : Zs) (hρ : Prime ρ), ρ ∣ (p : Zs) →
        (∀ r : ℚ, r ≠ 0 → vP ρ hρ (r : K0) = ((e * padicValRat p r : ℤ) : WithTop ℤ)) →
        ∀ g, Vge (vP ρ hρ) m ((W g)⁻¹ - 1) := by
      intro ρ hρ hρp hevρ g
      refine vge_inv_prod_sub_one Finset.univ hm1 fun j _ => ?_
      have hC := vge_normTests hρ hevρ hR0 ht1 (hD_old p hpS ρ hρ hρp g j)
      refine (vge_R_mul_sq hρ hevρ hR hC).mono ?_
      rw [hvR']
      -- the clearing inequality
      have hY : (v12 + 1 : ℤ) ≤ 2 * Ep p + padicValRat p R0 +
          2 * (0 - (prec j * padicValRat p R0 + (prec j + 1) * padicValRat p (t - 1))) := by
        rw [abs_le] at hold1 hold2
        rw [hvR0 p hp]
        rcases prec_cases j with hk | hk <;> rw [hk] <;> push_cast <;>
          nlinarith [hold1.1, hold1.2, hold2.1, hold2.2]
      have h0 : 0 ≤ v12 := Int.natCast_nonneg _
      have : e * (v12 + 1) ≤ e * (2 * Ep p + padicValRat p R0 +
          2 * (0 - (prec j * padicValRat p R0 + (prec j + 1) * padicValRat p (t - 1)))) :=
        mul_le_mul_of_nonneg_left hY (by linarith)
      nlinarith
    -- `Θ ≡ 12`
    set y : K0 := ∑ g, ((W g)⁻¹ - 1) with hy
    have hy1 : Vge (vP π hπ) m y := Vge.sum_of_le fun g _ => hWρ π hπ hπp hev g
    have hy2 : Vge (vP π hπ) m (star y) := by
      rw [Vge, ← vP_star]
      exact Vge.sum_of_le fun g _ => hWρ (star π) (prime_star hπ) (star_dvd_natCast hπp) hev' g
    have hΘ12 : ((Θ : ℚ) : K0) = 12 + (y + star y) := by
      rw [hΘK, hy, Finset.sum_sub_distrib, star_sub, Finset.sum_const]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show star ((6 : ℕ) * (1 : K0)) = (6 : ℕ) * (1 : K0) by simp]
      push_cast; ring
    have h12 : vP π hπ (12 : K0) = ((e * v12 : ℤ) : WithTop ℤ) := by
      rw [show (12 : K0) = ((12 : ℚ) : K0) by norm_num, hev 12 (by norm_num),
        show (12 : ℚ) = ((12 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    have hvΘK : vP π hπ ((Θ : ℚ) : K0) = ((e * v12 : ℤ) : WithTop ℤ) := by
      rw [hΘ12]; exact val_add_eq h12 (hy1.add hy2)
    rw [hev Θ hΘ] at hvΘK
    have hvΘ : padicValRat p Θ = v12 := by
      have := WithTop.coe_injective hvΘK
      exact mul_left_cancel₀ (by omega) this
    rw [hvB p hp, hvl, hva, hvΘ, hvR0 p hp]
    rw [abs_le] at hold2
    push_cast
    rw [hEp, hCp]
    nlinarith [hold2.1]
  ------------------------------------------------------------------
  -- Part 2: the selected primes
  have part2 : ∀ p : ℕ, p ∉ S_b → IsOddContactPrime t p → padicValRat p (R / Θ ^ 2) = 1 := by
    intro p hpS hodd
    have hp := hodd.1
    have : Fact p.Prime := ⟨hp⟩
    have hp324 := le_of_not_mem_S_b hp hpS
    have hp2 : p ≠ 2 := by omega
    obtain ⟨hF1, ht1v⟩ := padicValRat_contactQuot_eq_one ht hpS hodd
    have hvR0' : padicValRat p R0 = 1 := by rw [hvR0 p hp, hF1]
    have hva : padicValRat p a = 0 := by
      apply padicValRat_one_sub
      by_cases hq0 : q = 0
      · left; rw [hq0]; ring
      · right
        rw [padicValRat.mul hR0 (pow_ne_zero _ hq0), padicValRat.pow, hvR0']
        have := hq_sel p hpS hodd
        push_cast; linarith
    have hvl := hℓ p hp
    simp only [hpS, ↓reduceIte] at hvl
    have hvR' : padicValRat p R = 1 := by rw [hvR p hp, hvl, hva, hvR0']; ring
    obtain ⟨g₀, π, hπ, hπp, hDsel⟩ := hD_sel p hpS hodd
    have hev : ∀ r : ℚ, r ≠ 0 → vP π hπ (r : K0) = ((1 * padicValRat p r : ℤ) : WithTop ℤ) := by
      intro r hr; rw [one_mul]; exact vP_ratCast_odd hp2 hπ hπp hr
    have hev' : ∀ r : ℚ, r ≠ 0 →
        vP (star π) (prime_star hπ) (r : K0) = ((1 * padicValRat p r : ℤ) : WithTop ℤ) := by
      intro r hr; rw [vP_star hπ, star_ratCast, hev r hr]
    -- the residues `ε_ρ(g) ∈ {0, 1}`
    let εf : ∀ (ρ : Zs) (hρ : Prime ρ), Fin 6 → ℕ := fun ρ hρ g =>
      if ∀ j, Vge (vP ρ hρ) 0 (C g j) then 1 else 0
    have hεf : ∀ (ρ : Zs) (hρ : Prime ρ),
        (∀ r : ℚ, r ≠ 0 → vP ρ hρ (r : K0) = ((1 * padicValRat p r : ℤ) : WithTop ℤ)) →
        ∀ g, Vge (vP ρ hρ) 1 ((W g)⁻¹ - (εf ρ hρ g : K0)) := by
      intro ρ hρ hevρ g
      have hRρ : vP ρ hρ (R : K0) = 1 := by rw [hevρ R hR, hvR']; rfl
      have hsel := vge_inv_prod_selected (v := vP ρ hρ) Finset.univ hRρ (C := C g)
      by_cases hall : ∀ j, Vge (vP ρ hρ) 0 (C g j)
      · have : (εf ρ hρ g : K0) = 1 := by simp [εf, hall]
        rw [this]; exact hsel.1 fun j _ => hall j
      · have : (εf ρ hρ g : K0) = 0 := by simp [εf, hall]
        rw [this, sub_zero]
        push Not at hall
        obtain ⟨j, hj⟩ := hall
        exact hsel.2 ⟨j, Finset.mem_univ j, hj⟩
    have hε1 : εf π hπ g₀ = 1 := by
      have : ∀ j, Vge (vP π hπ) 0 (C g₀ j) := by
        intro j
        have := vge_normTests hπ hev hR0 ht1 (hDsel j)
        refine this.mono ?_
        rw [hvR0', ht1v]; ring_nf; exact le_rfl
      simp [εf, this]
    have hεle : ∀ ρ hρ g, εf ρ hρ g ≤ 1 := by intro ρ hρ g; simp only [εf]; split_ifs <;> simp
    set N : ℕ := ∑ g, εf π hπ g + ∑ g, εf (star π) (prime_star hπ) g with hN
    have hN1 : 1 ≤ N := by
      have : εf π hπ g₀ ≤ ∑ g, εf π hπ g :=
        Finset.single_le_sum (f := fun g => εf π hπ g) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ g₀)
      omega
    have hN12 : N ≤ 12 := by
      have h1 : ∑ g, εf π hπ g ≤ ∑ _g : Fin 6, 1 := Finset.sum_le_sum fun g _ => hεle _ _ g
      have h2 : ∑ g, εf (star π) (prime_star hπ) g ≤ ∑ _g : Fin 6, 1 :=
        Finset.sum_le_sum fun g _ => hεle _ _ g
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        mul_one] at h1 h2
      omega
    set y₁ : K0 := ∑ g, ((W g)⁻¹ - (εf π hπ g : K0)) with hy₁
    set y₂ : K0 := ∑ g, ((W g)⁻¹ - (εf (star π) (prime_star hπ) g : K0)) with hy₂
    have h1 : Vge (vP π hπ) 1 y₁ := Vge.sum_of_le fun g _ => hεf π hπ hev g
    have h2 : Vge (vP π hπ) 1 (star y₂) := by
      rw [Vge, ← vP_star]
      exact Vge.sum_of_le fun g _ => hεf (star π) (prime_star hπ) hev' g
    have hΘN : ((Θ : ℚ) : K0) = (N : K0) + (y₁ + star y₂) := by
      rw [hΘK, hy₁, hy₂, Finset.sum_sub_distrib, Finset.sum_sub_distrib, star_sub, hN,
        ← Nat.cast_sum, ← Nat.cast_sum, star_natCast, Nat.cast_add]
      generalize ∑ g, (W g)⁻¹ = S
      generalize ((∑ g, εf π hπ g : ℕ) : K0) = E1
      generalize ((∑ g, εf (star π) (prime_star hπ) g : ℕ) : K0) = E2
      ring
    have hNv : vP π hπ (N : K0) = ((0 : ℤ) : WithTop ℤ) := by
      have hN0 : (N : K0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [vP_apply hπ hN0, vp_natCast_of_not_dvd hπ hπp]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    have hvΘK : vP π hπ ((Θ : ℚ) : K0) = ((0 : ℤ) : WithTop ℤ) := by
      rw [hΘN]; exact val_add_eq hNv (by rw [zero_add]; exact h1.add h2)
    rw [hev Θ hΘ] at hvΘK
    have hvΘ : padicValRat p Θ = 0 := by
      have := WithTop.coe_injective hvΘK; rw [one_mul] at this; exact this
    rw [hvB p hp, hvl, hva, hvΘ, hvR0']; ring
  ------------------------------------------------------------------
  -- Part 3: the other primes
  have part3 : ∀ p : ℕ, p.Prime → p ∉ S_b → ¬ IsOddContactPrime t p →
      Even (padicValRat p (R / Θ ^ 2)) := by
    intro p hp hpS hodd
    rw [hvB p hp, hvR0 p hp]
    have he := even_padicValRat_contactQuot hp ht.not_mem_contactSet ht1 hodd
    have : 2 * padicValRat p ℓ + 2 * padicValRat p a +
        padicValRat p (contactPoly t / (t - 1) ^ 8) - 2 * padicValRat p Θ =
        2 * (padicValRat p ℓ + padicValRat p a - padicValRat p Θ) +
          padicValRat p (contactPoly t / (t - 1) ^ 8) := by ring
    rw [this]
    exact (even_two_mul _).add he
  ------------------------------------------------------------------
  rw [hB]
  refine ⟨part1, part2, part3, ?_, ?_⟩
  · intro p hp
    have hpS : p ∈ S_b := by
      refine mem_S_b.mpr (Or.inl (mem_S_ht.mpr ?_))
      simp only [poleS0, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have := part1 p hpS
    push_cast at this
    omega
  · apply isSquare_den_of_even
    intro p hp hneg
    by_cases hpS : p ∈ S_b
    · have := part1 p hpS; push_cast at this; omega
    by_cases hodd : IsOddContactPrime t p
    · have := part2 p hpS hodd; omega
    · exact part3 p hp hpS hodd

end ZInQ.Mult
