import ZInQKernel.Multiplication.Soundness.ContactValuations
import ZInQKernel.Multiplication.Certificate
import ZInQKernel.Multiplication.Local.PrimesAbove
import ZInQKernel.Multiplication.Local.Valuations

/-!
# The trace forces one common group and place

Blueprint: `multiplication/soundness/common-group.md`.

Let `t, η, q, R₀, a, R` be as in the slope predicate (`t ∉ 𝒞 ∪ {1}`, `a ≠ 0`), let
`D_{gj} ∈ K₀` (`g < 6`, `j < 12`) be arbitrary, `C_{gj} = D_{gj} / (R₀^{k_j} (t-1)^{k_j+1})`,
`W_g = ∏_j (1 + R C_{gj}²)` and `Θ = Tr Σ_g W_g⁻¹`, with `W_g ≠ 0`, `Θ ≠ 0` and `Φ(R/Θ²)`. At an
odd contact prime `p` of `t` with `p > 324` and `v_p(ℓ) = 0` (the article's `p ∉ S_b`), some
group `g` and some prime `π ∣ p` of `ℤ[s]` have `v_π(D_{gj}) ≥ k_j` for every `j`.

The quantities are the certificate's `slopeR0`, `slopeA`, `slopeR`, `normTests`, `groupW` and
`traceTheta`; `prec j = k_j`.
-/

namespace ZInQ.Mult

theorem vp_one' {π : Zs} (hπ : Prime π) : vp π (1 : K0) = 0 := by
  simpa using vp_isUnit hπ isUnit_one

section

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_π(1 + R C²) = min(0, r + 2 v_π(C))` when `v_π(R) = r` is odd and `C ≠ 0`. -/
theorem vp_one_add_mul_sq {π : Zs} (hπ : Prime π) {R C : K0} (hR : R ≠ 0) (hC : C ≠ 0)
    (hodd : Odd (vp π R)) : vp π (1 + R * C ^ 2) = min 0 (vp π R + 2 * vp π C) := by
  have hRC : R * C ^ 2 ≠ 0 := mul_ne_zero hR (pow_ne_zero _ hC)
  have hv : vp π (R * C ^ 2) = vp π R + 2 * vp π C := by
    rw [vp_mul hπ hR (pow_ne_zero _ hC), vp_pow hπ]; push_cast; ring
  rw [vp_add_eq_min_of_ne hπ one_ne_zero hRC (by
    rw [vp_one' hπ, hv]; obtain ⟨j, hj⟩ := hodd; omega), vp_one' hπ, hv]

/-- **The trace forces one common group and place.** -/
theorem common_group_of (hp324 : 324 < p) {t η q ℓ c : ℚ} (ht : t ∉ contactSet) (ht1 : t ≠ 1)
    (hη : η = 1 ∨ η = -1) (hℓ0 : ℓ ≠ 0) (hℓ : padicValRat p ℓ = 0)
    (ha : slopeA (slopeR0 η t) q ≠ 0) (D : Fin 6 → Fin 12 → K0)
    (hW : ∀ g, groupW (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t))
      (normTests (slopeR0 η t) t (D g)) ≠ 0)
    (hΘ : traceTheta (fun g => groupW (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t))
      (normTests (slopeR0 η t) t (D g))) ≠ 0)
    (hΦ : PoleSoluble (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t) /
      traceTheta (fun g => groupW (slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t))
        (normTests (slopeR0 η t) t (D g))) ^ 2))
    (hc : c ∈ contactSet) (hk : 0 < padicValRat p (t - c)) (hodd : Odd (padicValRat p (t - c))) :
    ∃ g : Fin 6, ∃ π : Zs, ∃ hπ : Prime π, π ∣ (p : Zs) ∧
      ∀ j, ((prec j : ℤ) : WithTop ℤ) ≤ vP π hπ (D g j) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, hone, hR₀v, -, hrodd, hrk⟩ :=
    contact_valuations_of (p := p) (by omega) ht ht1 hη hℓ0 hℓ ha hc hk hodd
  set k := padicValRat p (t - c) with hkdef
  set R₀ := slopeR0 η t with hR₀def
  set R := slopeR ℓ (slopeA (slopeR0 η t) q) (slopeR0 η t) with hRdef
  have hR₀0 : R₀ ≠ 0 := by
    intro h; rw [h, padicValRat.zero] at hR₀v; omega
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, padicValRat.zero] at hrodd; obtain ⟨i, hi⟩ := hrodd; omega
  set r := padicValRat p R with hrdef
  have hrodd' : Odd r := hrodd
  have hrk' : r ≤ k := hrk
  have ht10 : (t - 1 : ℚ) ≠ 0 := sub_ne_zero.mpr ht1
  -- valuations at a prime above `p`
  have hvq : ∀ {π : Zs} (hπ : Prime π), π ∣ (p : Zs) → ∀ x : ℚ, vp π (x : K0) = padicValRat p x :=
    fun hπ hπp x => vp_ratCast hp2 hπ hπp x
  -- the factors and their valuations
  set C : Fin 6 → Fin 12 → K0 := fun g j => normTests R₀ t (D g) j with hCdef
  set f : Fin 6 → Fin 12 → K0 := fun g j => 1 + (R : K0) * C g j ^ 2 with hfdef
  have hf0 : ∀ g j, f g j ≠ 0 := fun g j =>
    Finset.prod_ne_zero_iff.mp (hW g) j (Finset.mem_univ j)
  set W : Fin 6 → K0 := fun g => groupW R (normTests R₀ t (D g)) with hWdef
  have hWf : ∀ g, W g = ∏ j, f g j := fun g => rfl
  have hfle : ∀ {π : Zs} (hπ : Prime π), π ∣ (p : Zs) → ∀ g j, vp π (f g j) ≤ 0 := by
    intro π hπ hπp g j
    by_cases hC : C g j = 0
    · simp only [hfdef, hC]; simp [vp_one' hπ]
    · rw [hfdef]; dsimp only
      rw [vp_one_add_mul_sq hπ (Rat.cast_ne_zero.mpr hR0) hC (by rw [hvq hπ hπp]; exact hrodd')]
      exact min_le_left _ _
  -- `s(g, π) = v_π(W_g⁻¹) = -Σ_j v_π(f_{gj}) ≥ 0`
  have hWinv : ∀ {π : Zs} (hπ : Prime π), ∀ g,
      vp π (W g)⁻¹ = -∑ j, vp π (f g j) := by
    intro π hπ g
    rw [vp_inv hπ, hWf, vp_prod hπ _ _ fun j _ => hf0 g j]
  -- some group and place have `2 s < r`
  obtain ⟨π₀, hπ₀, hπ₀p⟩ := exists_prime_dvd_natCast p
  have hσ : Prime (star π₀) := prime_star hπ₀
  have hσp : star π₀ ∣ (p : Zs) := star_dvd_natCast hπ₀p
  have hex : ∃ g, ∃ π : Zs, ∃ hπ : Prime π, π ∣ (p : Zs) ∧
      2 * vp π (W g)⁻¹ < r := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    obtain ⟨i, hi⟩ := hrodd'
    have hge : ∀ {π : Zs} (hπ : Prime π), π ∣ (p : Zs) →
        Vge (vP π hπ) (i + 1) (∑ g, (W g)⁻¹) := by
      intro π hπ hπp
      apply Vge.sum_of_le
      intro g _
      have := hcon g π hπ hπp
      exact (le_vP_iff hπ _ _).mpr (Or.inr (by omega))
    set y := ∑ g, (W g)⁻¹ with hy
    have hy0 : y ≠ 0 := by
      intro h0; apply hΘ; rw [traceTheta]; rw [← hy, h0, map_zero]
    have h1 := ((le_vP_iff hπ₀ y _).mp (hge hπ₀ hπ₀p)).resolve_left hy0
    have h2 := ((le_vP_iff hσ y _).mp (hge hσ hσp)).resolve_left hy0
    have htr := (vp_trace_ge hp2 hπ₀ hπ₀p h1 h2).resolve_left (by rw [hy]; exact hΘ)
    -- the pole input has negative odd valuation
    have hB0 : R / traceTheta W ^ 2 ≠ 0 := div_ne_zero hR0 (pow_ne_zero _ hΘ)
    apply Mult.pole_obstruction _ hB0 hΦ p hp.out (by
      simp only [poleS0, Finset.mem_insert, Finset.mem_singleton]; omega)
    rw [padicValRat.div hR0 (pow_ne_zero _ hΘ), padicValRat.pow]
    change i + 1 ≤ padicValRat p (traceTheta W) at htr
    refine ⟨by push_cast; omega, ⟨i - padicValRat p (traceTheta W), by push_cast; omega⟩⟩
  obtain ⟨g, π, hπ, hπp, hs⟩ := hex
  refine ⟨g, π, hπ, hπp, fun j => ?_⟩
  set s := vp π (W g)⁻¹ with hsdef
  have hs0 : 0 ≤ s := by
    rw [hsdef, hWinv hπ]
    have := Finset.sum_nonpos (s := Finset.univ) fun j _ => hfle hπ hπp g j
    linarith
  by_cases hD : D g j = 0
  · rw [hD, (vP π hπ).map_zero]; exact le_top
  have hden : (R₀ : K0) ^ prec j * ((t - 1 : ℚ) : K0) ^ (prec j + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Rat.cast_ne_zero.mpr hR₀0)) (pow_ne_zero _ (Rat.cast_ne_zero.mpr ht10))
  have hC0 : C g j ≠ 0 := div_ne_zero hD hden
  set e := vp π (C g j) with he
  -- `4 e ≥ 1 - 3 r`
  have he4 : 1 - 3 * r ≤ 4 * e := by
    have hf := vp_one_add_mul_sq hπ (Rat.cast_ne_zero.mpr hR0) hC0
      (by rw [hvq hπ hπp]; exact hrodd')
    rw [hvq hπ hπp] at hf
    obtain ⟨i, hi⟩ := hrodd'
    by_cases hpos : 0 < r + 2 * e
    · omega
    · have hfj : vp π (f g j) = r + 2 * e := by
        show vp π (1 + (R : K0) * C g j ^ 2) = _
        rw [hf, ← hrdef, ← he]; omega
      have hsum : ∑ j', vp π (f g j') ≤ vp π (f g j) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        have := Finset.sum_nonpos (s := Finset.univ.erase j) fun j' _ => hfle hπ hπp g j'
        linarith
      have : s = -∑ j', vp π (f g j') := by rw [hsdef, hWinv hπ]
      omega
  -- `v_π(D) = e + k_j k`
  have hDeq : D g j = C g j * ((R₀ : K0) ^ prec j * ((t - 1 : ℚ) : K0) ^ (prec j + 1)) := by
    simp only [hCdef, normTests]
    rw [div_mul_cancel₀ _ hden]
  have hDv : vp π (D g j) = e + prec j * k := by
    rw [hDeq, vp_mul hπ hC0 hden,
      vp_mul hπ (pow_ne_zero _ (Rat.cast_ne_zero.mpr hR₀0)) (pow_ne_zero _ (Rat.cast_ne_zero.mpr ht10)),
      vp_pow hπ, vp_pow hπ, hvq hπ hπp, hvq hπ hπp, hR₀v, hone, ← he]
    ring
  rw [vP_apply hπ hD, hDv, WithTop.coe_le_coe]
  have hk1 : 1 ≤ k := hk
  unfold prec
  split_ifs <;> push_cast <;> omega

/-- **The trace forces one common group and place**, with `ℓ = ℓ₀` and `p ∉ S_b`. -/
theorem common_group (hpS : p ∉ S_b) {t η q c : ℚ} (ht : t ∉ contactSet) (ht1 : t ≠ 1)
    (hη : η = 1 ∨ η = -1) (ha : slopeA (slopeR0 η t) q ≠ 0) (D : Fin 6 → Fin 12 → K0)
    (hW : ∀ g, groupW (slopeR (Syntax.ell : ℚ) (slopeA (slopeR0 η t) q) (slopeR0 η t))
      (normTests (slopeR0 η t) t (D g)) ≠ 0)
    (hΘ : traceTheta (fun g => groupW (slopeR (Syntax.ell : ℚ) (slopeA (slopeR0 η t) q)
      (slopeR0 η t)) (normTests (slopeR0 η t) t (D g))) ≠ 0)
    (hΦ : PoleSoluble (slopeR (Syntax.ell : ℚ) (slopeA (slopeR0 η t) q) (slopeR0 η t) /
      traceTheta (fun g => groupW (slopeR (Syntax.ell : ℚ) (slopeA (slopeR0 η t) q)
        (slopeR0 η t)) (normTests (slopeR0 η t) t (D g))) ^ 2))
    (hc : c ∈ contactSet) (hk : 0 < padicValRat p (t - c)) (hodd : Odd (padicValRat p (t - c))) :
    ∃ g : Fin 6, ∃ π : Zs, ∃ hπ : Prime π, π ∣ (p : Zs) ∧
      ∀ j, ((prec j : ℤ) : WithTop ℤ) ≤ vP π hπ (D g j) :=
  common_group_of (lt_of_not_mem_S_b hp.out hpS) ht ht1 hη ell_cast_ne_zero
    (padicValRat_ell_of_not_mem hpS) ha D hW hΘ hΦ hc hk hodd

end

end ZInQ.Mult
