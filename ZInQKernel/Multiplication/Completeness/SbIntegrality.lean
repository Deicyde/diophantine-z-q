import ZInQKernel.Multiplication.Completeness.TestsLocal
import ZInQKernel.Multiplication.Certificate.ConstantsProperties

/-!
# Integrality of the tests at the old primes

Blueprint: `multiplication/completeness/sb-integrality.md`.

`Q₀ = [M₀]P₀` has `1/x(Q₀) = (a + b s)/c` with `N_s⁴ ∣ a, b` and `gcd(c, N_s) = 1`, so at every
prime `ρ` of `ℤ[s]` above a prime of `S_b` (all of which divide `N_s = P_s H_cat`), `x(Q₀)` has
negative valuation: `Q₀` is formal at `ρ`. If `M₀ ∣ h`, `h ≠ 0`, `h ≠ c_*`, then `H = [h]P₀` and
`V₀ = [h - c_*]P₀` are nonzero multiples of `Q₀`, hence formal at `ρ` and at `σρ`, and the twelve
tests are `ρ`-integral (`tests_vge_zero_of_W1`).
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

/-- Every prime of `S_b` divides `N_s = P_s H_cat`. -/
theorem dvd_Ns_of_mem_S_b {p : ℕ} (hp : p ∈ S_b) : p ∣ Syntax.Ns := by
  rw [Syntax.Ns_eq]
  rcases mem_S_b.mp hp with h | h
  · obtain ⟨hpp, hp324⟩ := mem_S_ht.mp h
    have : p ∣ Syntax.Ps := by rw [Syntax.Ps_eq]; exact hpp.dvd_primorial_iff.mpr hp324
    exact Nat.dvd_trans this (Nat.dvd_mul_right _ _)
  · have : p ∣ Syntax.Hcat := by
      rw [Syntax.Hcat_eq_catalogueModulus, Syntax.catalogueProduct_eq_prod_catalogueFinset]
      exact Finset.dvd_prod_of_mem _ (by rw [← catalogue_eq]; exact h)
    exact Nat.dvd_trans this (Nat.dvd_mul_left _ _)

/-- The formal condition holds at `M₀` once `M₀ ≥ 1`. -/
theorem formalCondition_M0 (hM : 1 ≤ Syntax.M0) : Syntax.FormalCondition Syntax.Ns Syntax.M0 := by
  have h : ∃ m, 1 ≤ m ∧ Syntax.FormalCondition Syntax.Ns m := by
    rw [← Syntax.leastFormalMultiple_pos_iff, ← Syntax.M0_eq]; omega
  exact (Syntax.M0_spec h).2.1

/-- **`Q₀ = [M₀]P₀` is formal** at every prime `ρ` of `ℤ[s]` above a prime of `S_b`. -/
theorem Q0_mem_W1 (hM : 1 ≤ Syntax.M0) {p : ℕ} (hp : p ∈ S_b) {ρ : Zs} (hρ : Prime ρ)
    (hρp : ρ ∣ (p : Zs)) : ((Syntax.M0 : ℤ) • genP0) ∈ W1 (vP ρ hρ) (-genD ^ 2) := by
  have hpp := prime_of_mem_S_b hp
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨ha, hb, hc⟩ := formalCondition_M0 hM
  obtain ⟨x, y, hxy, hQ, hx0, -, -⟩ := log25_z_ne_zero (n := (Syntax.M0 : ℤ)) (by omega)
  rw [natCast_zsmul] at hQ
  rw [hQ] at ha hb hc
  rw [natCast_zsmul, hQ]
  show vP ρ hρ x < 0
  simp only [Syntax.xi_some] at ha hb hc
  obtain ⟨hc0, -, hrep⟩ := Syntax.normalizedRep_isNormalizedRep x⁻¹
  set a := (Syntax.normalizedRep x⁻¹).1
  set b := (Syntax.normalizedRep x⁻¹).2.1
  set c := (Syntax.normalizedRep x⁻¹).2.2
  obtain ⟨a', ha'⟩ := ha
  obtain ⟨b', hb'⟩ := hb
  -- `ρ ∣ N_s` and `ρ ∤ c`
  have hρN : ρ ∣ (Syntax.Ns : Zs) := hρp.trans (Nat.cast_dvd_cast (dvd_Ns_of_mem_S_b hp))
  have hpc : ¬ p ∣ c := fun h => by
    have := Nat.dvd_gcd h (dvd_Ns_of_mem_S_b hp)
    rw [hc.gcd_eq_one] at this
    exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
  have hvc : vp ρ (c : K0) = 0 := vp_natCast_of_not_dvd hρ hρp hpc
  -- the numerator `N_s⁴ (a' + b' s)`
  have hnum : ((a : ℤ) : K0) + ((b : ℤ) : K0) * sqrt2 =
      Zs.toK0 ((Syntax.Ns : Zs) ^ 4 * ⟨a', b'⟩) := by
    have hw : Zs.toK0 (⟨a', b'⟩ : Zs) = (a' : K0) + (b' : K0) * sqrt2 := by
      ext <;> simp [sqrt2]
    rw [map_mul, map_pow, map_natCast, hw, ha', hb']
    push_cast; ring
  have hxinv : x⁻¹ ≠ 0 := inv_ne_zero hx0
  have hnum0 : ((Syntax.Ns : Zs) ^ 4 * ⟨a', b'⟩ : Zs) ≠ 0 := by
    intro h0
    apply hxinv
    rw [hrep, hnum, h0, map_zero, zero_div]
  have hvN : 1 ≤ vp ρ (Zs.toK0 (Syntax.Ns : Zs)) :=
    (vp_pos_iff hρ (by exact_mod_cast Syntax.Ns_pos.ne')).mpr hρN
  have hvnum : 4 ≤ vp ρ (Zs.toK0 ((Syntax.Ns : Zs) ^ 4 * ⟨a', b'⟩)) := by
    have hNs0 : Zs.toK0 (Syntax.Ns : Zs) ≠ 0 := by
      rw [map_natCast]; exact_mod_cast Syntax.Ns_pos.ne'
    have hw0 : Zs.toK0 (⟨a', b'⟩ : Zs) ≠ 0 := by
      intro h; apply hnum0; rw [(map_eq_zero_iff _ Zs.toK0_injective).mp h, mul_zero]
    rw [map_mul, map_pow, vp_mul hρ (pow_ne_zero _ hNs0) hw0, vp_pow hρ]
    have := vp_nonneg hρ (⟨a', b'⟩ : Zs)
    push_cast
    rw [map_natCast] at hvN
    linarith
  have hvxinv : 4 ≤ vp ρ x⁻¹ := by
    rw [hrep, hnum, vp_div hρ (by rwa [ne_eq, map_eq_zero_iff _ Zs.toK0_injective])
      (by exact_mod_cast hc0.ne'), hvc, sub_zero]
    exact hvnum
  rw [vp_inv hρ] at hvxinv
  rw [vP_apply hρ hx0]
  exact WithTop.coe_lt_coe.mpr (by omega)

/-- **Integrality of the tests at the old primes.** If `M₀ ∣ h`, `h ≠ 0` and `h ≠ c_*`, then for
all `n₁, n₂, n₃` the twelve tests `τ(h, (n_i h); c_*, c_* n_i)` are integral at every prime of
`ℤ[s]` above a prime of `S_b`. -/
theorem tests_integral_old (n : Fin 3 → ℤ) (h : ℤ) (hM : (Syntax.M0 : ℤ) ∣ h) (h0 : h ≠ 0)
    (hc : h ≠ Syntax.cstar) {p : ℕ} (hp : p ∈ S_b) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs))
    (j : Fin 12) : Vge (vP π hπ) 0 (testValues h (fun i => n i * h) (certShifts n) j) := by
  have hM1 : 1 ≤ Syntax.M0 := by
    rcases Nat.eq_zero_or_pos Syntax.M0 with h' | h'
    · rw [h', Nat.cast_zero, zero_dvd_iff] at hM; exact absurd hM h0
    · exact h'
  obtain ⟨k, rfl⟩ := hM
  have hc0 : certShifts n 0 = (Syntax.cstar : ℤ) := rfl
  have hcs : (Syntax.cstar : ℤ) = 4 * Syntax.M0 := by rw [Syntax.cstar_eq]; push_cast; ring
  have hH : (↑Syntax.M0 * k) • genP0 = k • ((Syntax.M0 : ℤ) • genP0) := by
    rw [smul_smul, mul_comm]
  have hV : (↑Syntax.M0 * k - certShifts n 0) • genP0 = (k - 4) • ((Syntax.M0 : ℤ) • genP0) := by
    rw [smul_smul, hc0, hcs]; congr 1; ring
  refine tests_vge_zero_of_W1 hπ _ _ _ n (fun i => by rw [smul_smul])
    (fun i => ?_) ?_ (zsmul_genP0_ne_zero h0) ?_ ?_ j
  · have : certShifts n i.succ = Syntax.cstar * n i := by
      fin_cases i <;> rfl
    rw [this, hc0, smul_smul]; congr 1; ring
  · rw [hH]
    exact (zsmul_mem_W1 (vP_neg_genD_sq_nonneg hπ) (Q0_mem_W1 hM1 hp hπ hπp) k).1
  · rw [hV]
    exact (zsmul_mem_W1 (vP_neg_genD_sq_nonneg (prime_star hπ))
      (Q0_mem_W1 hM1 hp (prime_star hπ) (star_dvd_natCast hπp)) (k - 4)).1
  · refine zsmul_genP0_ne_zero ?_
    rw [hc0, hcs]
    intro h'
    apply hc
    rw [hcs]; linarith

end ZInQ.Mult
