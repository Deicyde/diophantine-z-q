import ZInQKernel.Contrib.OneProof.EichlerBound.Order

/-! eichler-bound, part C: an order `R` of conductor prime to `6` in a quadratic field `k` is `ℤ + ℤω`, and
the arithmetic of `ω` at `2` and `3` (no `sorry`). -/

set_option linter.style.longLine false

noncomputable section

namespace EichlerBound

open LeafQM LeafQM.AV

section NT

variable {k : Type} [Field k] [NumberField k]

/-- An integral element of a quadratic field satisfies `r² − t r + n = 0` with `t, n ∈ ℤ` (copied from
`GR56.quad_rel`). -/
theorem quad_rel (hk : Module.finrank ℚ k = 2) (r : k) (hr : IsIntegral ℤ r) :
    ∃ t n : ℤ, r * r - (t : k) * r + (n : k) = 0 := by
  have hm := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hr
  have hdeg : (minpoly ℚ r).natDegree ≤ 2 := hk ▸ minpoly.natDegree_le r
  have hmon : (minpoly ℤ r).Monic := minpoly.monic hr
  have hpd : (minpoly ℤ r).natDegree ≤ 2 := by
    rw [hm, Polynomial.natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int] at hdeg
    exact hdeg
  have hpos : 0 < (minpoly ℤ r).natDegree := minpoly.natDegree_pos hr
  have hev : Polynomial.aeval r (minpoly ℤ r) = 0 := minpoly.aeval ℤ r
  have hlc : (minpoly ℤ r).coeff (minpoly ℤ r).natDegree = 1 := hmon.coeff_natDegree
  rw [Polynomial.aeval_eq_sum_range] at hev
  generalize (minpoly ℤ r) = p at *
  interval_cases h : p.natDegree
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at hev
    rw [hlc, one_smul, zsmul_eq_mul, mul_one] at hev
    refine ⟨-2 * p.coeff 0, p.coeff 0 * p.coeff 0, ?_⟩
    have : r = -(p.coeff 0 : k) := by linear_combination hev
    rw [this]; push_cast; ring
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at hev
    rw [hlc, one_smul, zsmul_eq_mul, zsmul_eq_mul, mul_one] at hev
    refine ⟨-p.coeff 1, p.coeff 0, ?_⟩
    push_cast
    linear_combination hev

/-- Every element of `k` has a positive integer multiple in an order of conductor prime to `6`
(copied from `GR56.exists_nat_mul_mem`). -/
theorem exists_nat_mul_mem (R : Subring k) (hc : Nat.Coprime (conductor R) 6) (a : k) :
    ∃ n : ℕ, 0 < n ∧ (n : k) * a ∈ R := by
  have hc0 : conductor R ≠ 0 := by
    intro h0; rw [h0] at hc; norm_num at hc
  have hx : IsAlgebraic ℤ a := IsFractionRing.isAlgebraic_iff ℤ ℚ k |>.mpr (.of_finite ℚ a)
  obtain ⟨m, s, hm, hms⟩ := hx.exists_nsmul_eq (integralClosure ℤ k)
  have hmem : m • a ∈ (integralClosure ℤ k).toSubring.toAddSubgroup := by
    rw [hms]; exact s.2
  have h2 := R.toAddSubgroup.nsmul_relIndex_mem hmem
  refine ⟨conductor R * m, Nat.mul_pos (Nat.pos_of_ne_zero hc0) (Nat.pos_of_ne_zero hm), ?_⟩
  have : (((conductor R * m : ℕ)) : k) * a = conductor R • (m • a) := by
    rw [smul_smul, nsmul_eq_mul]
  rw [this]
  exact h2

/-- An element of `k` outside `ℚ` (copied from `GR56.exists_not_rat`). -/
theorem exists_not_rat (hk : Module.finrank ℚ k = 2) : ∃ a : k, ∀ r : ℚ, a ≠ algebraMap ℚ k r := by
  by_contra h
  push Not at h
  have hs : Function.Surjective (Algebra.linearMap ℚ k) := fun a => by
    obtain ⟨r, hr⟩ := h a; exact ⟨r, hr.symm⟩
  let e := LinearEquiv.ofBijective (Algebra.linearMap ℚ k) ⟨(algebraMap ℚ k).injective, hs⟩
  have := e.finrank_eq
  rw [Module.finrank_self, hk] at this
  norm_num at this

/-- `k = ℚ ⊕ ℚ a₁` for `a₁ ∉ ℚ` (copied from `GR56.decomp`). -/
theorem decomp (hk : Module.finrank ℚ k = 2) {a1 : k} (ha1 : ∀ r : ℚ, a1 ≠ algebraMap ℚ k r) (a : k) :
    ∃ s t : ℚ, a = algebraMap ℚ k s + t • a1 := by
  have hli : LinearIndependent ℚ ![(1 : k), a1] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro r h
    apply ha1 r
    rw [← h, Algebra.smul_def, mul_one]
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [hk])
  have hmem : a ∈ Submodule.span ℚ (Set.range ![(1 : k), a1]) := hspan ▸ Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc]
  simp [Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one]

/-- Coordinates in `ℚ ⊕ ℚ a₁` are unique. -/
theorem coord_unique {a1 : k} (ha1 : ∀ r : ℚ, a1 ≠ algebraMap ℚ k r) {x y x' y' : ℚ}
    (h : (x : k) + (y : k) * a1 = (x' : k) + (y' : k) * a1) : x = x' ∧ y = y' := by
  have hy : y = y' := by
    by_contra hne
    apply ha1 ((x' - x) / (y - y'))
    have hne' : ((y : k) - y') ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hne
    rw [eq_ratCast]
    push_cast
    field_simp
    linear_combination h
  subst hy
  refine ⟨?_, rfl⟩
  have : (x : k) = x' := by linear_combination h
  exact_mod_cast this

/-- A rational number integral over `ℤ` (inside `k`) is an integer. -/
theorem int_of_integral_rat {q : ℚ} (h : IsIntegral ℤ (algebraMap ℚ k q)) : ∃ z : ℤ, q = z := by
  have h' : IsIntegral ℤ q := isIntegral_algebraMap_iff.mp h
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  exact ⟨z, by rw [← hz]; simp⟩

/-- A rational whose square is an integer is an integer. -/
theorem rat_int_of_sq {q : ℚ} {z : ℤ} (h : q ^ 2 = z) : ∃ w : ℤ, q = w := by
  have hd : (q ^ 2).den = 1 := by rw [h]; rfl
  rw [Rat.den_pow] at hd
  have : q.den = 1 := by
    rcases Nat.lt_or_ge q.den 2 with h1 | h1
    · have := q.den_pos; omega
    · have : 2 ^ 2 ≤ q.den ^ 2 := Nat.pow_le_pow_left h1 2
      omega
  exact ⟨q.num, (Rat.coe_int_num_of_den_eq_one this).symm⟩

theorem isIntegral_of_quad {z : k} {T M : ℤ} (h : z * z - (T : k) * z + (M : k) = 0) : IsIntegral ℤ z := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C T * Polynomial.X + Polynomial.C M, ?_, ?_⟩
  · have : (Polynomial.X ^ 2 - Polynomial.C T * Polynomial.X + Polynomial.C M : Polynomial ℤ) =
        Polynomial.X ^ 2 + (Polynomial.C (-T) * Polynomial.X + Polynomial.C M) := by
      simp only [map_neg]; ring
    rw [this]
    exact Polynomial.monic_X_pow_add (by
      refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by norm_num)
      · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num))
  · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_X_pow]
    simp only [eq_intCast]
    linear_combination h

/-- **An order of conductor prime to 6 is `ℤ + ℤω`.** -/
theorem exists_basis (hk : Module.finrank ℚ k = 2) (R : Subring k)
    (hR : R ≤ (integralClosure ℤ k).toSubring) (hc : Nat.Coprime (conductor R) 6) :
    ∃ ω ∈ R, (∀ q : ℚ, ω ≠ algebraMap ℚ k q) ∧ ∀ r ∈ R, ∃ x y : ℤ, r = (x : k) + (y : k) * ω := by
  obtain ⟨a, ha⟩ := exists_not_rat hk
  obtain ⟨m, hm, hma⟩ := exists_nat_mul_mem R hc a
  set a1 := (m : k) * a with ha1def
  have ha1 : ∀ r : ℚ, a1 ≠ algebraMap ℚ k r := by
    intro r hr
    apply ha (r / m)
    have hm' : (m : k) ≠ 0 := by exact_mod_cast hm.ne'
    rw [eq_ratCast] at hr ⊢
    push_cast
    field_simp
    rw [mul_comm]; exact hr
  have hint : ∀ r ∈ R, IsIntegral ℤ r := fun r hr =>
    hR hr
  obtain ⟨t1, n1, h1⟩ := quad_rel hk a1 (hint _ hma)
  set D : ℤ := t1 ^ 2 - 4 * n1 with hD
  have hD0 : D ≠ 0 := by
    intro h0
    apply ha1 (t1 / 2)
    rw [eq_ratCast]; push_cast
    have : (a1 - (t1 : k) / 2) * (a1 - (t1 : k) / 2) = 0 := by
      have h0' : ((t1 : k) ^ 2 - 4 * n1) = 0 := by exact_mod_cast h0
      linear_combination h1 + h0' / 4
    have := mul_self_eq_zero.mp this
    linear_combination this
  -- the `a₁`-coordinate of an element of `R` lies in `D⁻¹ ℤ`
  have hcoord : ∀ r ∈ R, ∃ x y : ℚ, r = (x : k) + (y : k) * a1 ∧ ∃ z : ℤ, (D : ℚ) * y = z := by
    intro r hr
    obtain ⟨x, y, hxy⟩ := decomp hk ha1 r
    rw [eq_ratCast, Rat.smul_def] at hxy
    refine ⟨x, y, hxy, ?_⟩
    obtain ⟨tr, nr, hrn⟩ := quad_rel hk r (hint r hr)
    by_cases hy : y = 0
    · exact ⟨0, by rw [hy]; simp⟩
    · -- compare coefficients in `r² − tr r + nr = 0`
      have e : ((x ^ 2 - y ^ 2 * n1 - tr * x + nr : ℚ) : k) + ((2 * x * y + y ^ 2 * t1 - tr * y : ℚ) : k) * a1 =
          ((0 : ℚ) : k) + ((0 : ℚ) : k) * a1 := by
        push_cast
        rw [hxy] at hrn
        linear_combination hrn - (y : k) ^ 2 * h1
      obtain ⟨e1, e2⟩ := coord_unique ha1 e
      have htr : (tr : ℚ) = 2 * x + y * t1 := by
        have : y * ((tr : ℚ) - (2 * x + y * t1)) = 0 := by linear_combination -e2
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hy
        · linarith
      have hnr : (nr : ℚ) = x ^ 2 + t1 * x * y + n1 * y ^ 2 := by
        rw [htr] at e1; linarith
      have hsq : ((D : ℚ) * y) ^ 2 = ((D * (tr ^ 2 - 4 * nr) : ℤ) : ℚ) := by
        push_cast; rw [htr, hnr, hD]; push_cast; ring
      exact rat_int_of_sq hsq
  -- the minimal positive value of `D y`
  have hex : ∃ h : ℕ, 0 < h ∧ ∃ r ∈ R, ∃ x y : ℚ, r = (x : k) + (y : k) * a1 ∧ (D : ℚ) * y = h := by
    rcases lt_or_gt_of_ne hD0 with hneg | hpos
    · refine ⟨D.natAbs, by omega, -a1, R.neg_mem hma, 0, -1, by push_cast; ring, ?_⟩
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]; ring
    · refine ⟨D.natAbs, by omega, a1, hma, 0, 1, by push_cast; ring, ?_⟩
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]; ring
  classical
  obtain ⟨h0, ⟨hpos, ω, hω, xω, yω, hωxy, hωD⟩, hmin⟩ : ∃ h0 : ℕ, (0 < h0 ∧ ∃ r ∈ R, ∃ x y : ℚ,
      r = (x : k) + (y : k) * a1 ∧ (D : ℚ) * y = h0) ∧ ∀ h < h0, ¬ (0 < h ∧ ∃ r ∈ R, ∃ x y : ℚ,
      r = (x : k) + (y : k) * a1 ∧ (D : ℚ) * y = h) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun h hh => Nat.find_min hex hh⟩
  refine ⟨ω, hω, ?_, ?_⟩
  · intro q hq
    have e : (xω : k) + (yω : k) * a1 = (q : k) + ((0 : ℚ) : k) * a1 := by
      rw [← hωxy, hq, eq_ratCast]; simp
    obtain ⟨-, e2⟩ := coord_unique ha1 e
    rw [e2, mul_zero] at hωD
    have h00 : (h0 : ℚ) = 0 := hωD.symm
    norm_cast at h00; omega
  · intro r hr
    obtain ⟨x, y, hxy, z, hz⟩ := hcoord r hr
    set q := z / (h0 : ℤ)
    set rem := z % (h0 : ℤ)
    have hrem0 : 0 ≤ rem := Int.emod_nonneg _ (by omega)
    have hrem1 : rem < h0 := Int.emod_lt_of_pos _ (by omega)
    have hzq : z = (h0 : ℤ) * q + rem := (Int.mul_ediv_add_emod z h0).symm
    have hmem : r - (q : k) * ω ∈ R := R.sub_mem hr (R.mul_mem (_root_.intCast_mem R q) hω)
    have hexp : r - (q : k) * ω = ((x - q * xω : ℚ) : k) + ((y - q * yω : ℚ) : k) * a1 := by
      rw [hxy, hωxy]; push_cast; ring
    have hDy : (D : ℚ) * (y - q * yω) = rem := by
      rw [mul_sub, hz, ← mul_assoc, mul_comm (D : ℚ) q, mul_assoc, hωD, hzq]; push_cast; ring
    have hrem : rem = 0 := by
      by_contra hne
      have hlt : rem.toNat < h0 := by omega
      have := hmin _ hlt
      apply this
      refine ⟨by omega, _, hmem, _, _, hexp, ?_⟩
      rw [hDy]; exact_mod_cast (Int.toNat_of_nonneg hrem0).symm
    have hy0 : y - q * yω = 0 := by
      rw [hrem] at hDy
      have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
      simpa [hD'] using hDy
    rw [hy0] at hexp
    simp only [Rat.cast_zero, zero_mul, add_zero] at hexp
    obtain ⟨w, hw⟩ := int_of_integral_rat (k := k) (q := x - q * yω * 0 - q * xω + q * yω * 0) (by
      rw [show x - q * yω * 0 - q * xω + q * yω * 0 = x - q * xω by ring, eq_ratCast, ← hexp]
      exact hint _ hmem)
    refine ⟨w, q, ?_⟩
    have : r = ((x - q * xω : ℚ) : k) + (q : k) * ω := by rw [← hexp]; ring
    rw [this]
    have hw' : x - q * xω = (w : ℚ) := by linarith
    rw [hw']; push_cast; ring

/-- `f • z ∈ R` for `z ∈ 𝒪_k`, `f` the conductor. -/
theorem conductor_smul_mem (R : Subring k) {z : k} (hz : IsIntegral ℤ z) : (conductor R : ℤ) • z ∈ R := by
  have hmem : z ∈ (integralClosure ℤ k).toSubring.toAddSubgroup := hz
  have := R.toAddSubgroup.nsmul_relIndex_mem hmem
  rw [natCast_zsmul]; exact this

/-- If `z ∈ 𝒪_k` and `ℓ z ∈ R` with `ℓ ∈ {2, 3}` prime to the conductor, then `z ∈ R`. -/
theorem mem_of_ell_mul (R : Subring k) (hc : Nat.Coprime (conductor R) 6) {ℓ : ℤ} (hℓ : L6 ℓ) {z : k}
    (hz : IsIntegral ℤ z) (hℓz : (ℓ : k) * z ∈ R) : z ∈ R := by
  have hcop : IsCoprime (conductor R : ℤ) ℓ := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    rcases hℓ with rfl | rfl
    · have : Nat.Coprime (conductor R) 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hc
      exact_mod_cast this
    · have : Nat.Coprime (conductor R) 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hc
      exact_mod_cast this
  obtain ⟨u, v, huv⟩ := hcop
  have h1 := conductor_smul_mem R hz
  have : z = (u : k) * ((conductor R : ℤ) • z) + (v : k) * ((ℓ : k) * z) := by
    rw [zsmul_eq_mul]
    have : ((u * (conductor R : ℤ) + v * ℓ : ℤ) : k) = 1 := by rw [huv]; simp
    push_cast at this
    simp only [Int.cast_natCast] at this ⊢
    linear_combination -z * this
  rw [this]
  exact R.add_mem (R.mul_mem (_root_.intCast_mem R u) h1) (R.mul_mem (_root_.intCast_mem R v) hℓz)

/-- **The ramified element**: if `ℓ ∈ {2, 3}` divides `Δ = t² − 4n` and not the conductor, some `ω − a ∈ R` has
norm `a² − t a + n` exactly divisible by `ℓ`. -/
theorem exists_l (R : Subring k) (hc : Nat.Coprime (conductor R) 6) {ω : k} (hωR : ω ∈ R)
    (hω : ∀ q : ℚ, ω ≠ algebraMap ℚ k q) (hbasis : ∀ r ∈ R, ∃ x y : ℤ, r = (x : k) + (y : k) * ω)
    {t n : ℤ} (htn : ω * ω - (t : k) * ω + (n : k) = 0) {ℓ : ℤ} (hℓ : L6 ℓ) (hΔ : ℓ ∣ t ^ 2 - 4 * n) :
    ∃ a : ℤ, ℓ ∣ a ^ 2 - t * a + n ∧ ¬ ℓ ^ 2 ∣ a ^ 2 - t * a + n := by
  obtain ⟨a, hT, hN⟩ : ∃ a : ℤ, ℓ ∣ t - 2 * a ∧ ℓ ∣ a ^ 2 - t * a + n := by
    rcases hℓ with rfl | rfl
    · have ht : (2 : ℤ) ∣ t := by
        have : (2 : ℤ) ∣ t ^ 2 := by
          have := dvd_add hΔ (dvd_mul_of_dvd_left (by norm_num : (2 : ℤ) ∣ 4) n); simpa using this
        exact Int.prime_two.dvd_of_dvd_pow this
      obtain ⟨t', rfl⟩ := ht
      refine ⟨n, ⟨t' - n, by ring⟩, ?_⟩
      have : (2 : ℤ) ∣ n * (n + 1) := by
        rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
        · exact ⟨m * (n + 1), by rw [hm]; ring⟩
        · exact ⟨n * (m + 1), by rw [hm]; ring⟩
      obtain ⟨w, hw⟩ := this
      exact ⟨w - t' * n, by linear_combination hw⟩
    · refine ⟨2 * t, ⟨-t, by ring⟩, ?_⟩
      obtain ⟨w, hw⟩ := hΔ
      exact ⟨3 * n + 2 * w, by linear_combination 2 * hw⟩
  refine ⟨a, hN, ?_⟩
  rintro ⟨M, hM⟩
  obtain ⟨T, hT⟩ := hT
  have hℓ0 : (ℓ : k) ≠ 0 := by rcases hℓ with rfl | rfl <;> norm_num
  set z : k := (ω - a) / ℓ with hz
  have hquad : z * z - (T : k) * z + (M : k) = 0 := by
    have e1 : (ℓ : k) * z = ω - a := by rw [hz]; field_simp
    have hT' : (t : k) - 2 * a = ℓ * T := by exact_mod_cast hT
    have hM' : (a : k) ^ 2 - t * a + n = ℓ ^ 2 * M := by exact_mod_cast hM
    have : (ℓ : k) ^ 2 * (z * z - (T : k) * z + (M : k)) = ω * ω - (t : k) * ω + (n : k) := by
      have h2 : (ℓ : k) ^ 2 * (z * z - (T : k) * z + (M : k)) =
          ((ℓ : k) * z) * ((ℓ : k) * z) - ((ℓ : k) * T) * ((ℓ : k) * z) + (ℓ : k) ^ 2 * M := by ring
      rw [h2, e1, ← hT', ← hM']; ring
    rw [htn] at this
    have hℓ2 : (ℓ : k) ^ 2 ≠ 0 := pow_ne_zero 2 hℓ0
    exact (mul_eq_zero.mp this).resolve_left hℓ2
  have hzR : z ∈ R := by
    refine mem_of_ell_mul R hc hℓ (isIntegral_of_quad hquad) ?_
    have : (ℓ : k) * z = ω - a := by rw [hz]; field_simp
    rw [this]; exact R.sub_mem hωR (_root_.intCast_mem R a)
  obtain ⟨x, y, hxy⟩ := hbasis z hzR
  have e : ((-a : ℚ) : k) + ((1 : ℚ) : k) * ω = (((ℓ * x : ℤ) : ℚ) : k) + (((ℓ * y : ℤ) : ℚ) : k) * ω := by
    have : (ℓ : k) * z = ω - a := by rw [hz]; field_simp
    push_cast
    rw [← sub_eq_zero]
    have h' := congrArg (fun w => (ℓ : k) * w) hxy
    rw [this] at h'
    linear_combination h'
  obtain ⟨-, e2⟩ := coord_unique hω e
  have : ℓ * y = 1 := by exact_mod_cast e2.symm
  have hd : ℓ ∣ 1 := ⟨y, this.symm⟩
  rcases hℓ with rfl | rfl <;> norm_num at hd

theorem zmod2_aux : ∀ x y x' y' t n : ZMod 2, 2 * x + t * y = 0 → x ^ 2 + t * x * y + n * y ^ 2 = 0 →
    2 * x' + t * y' = 0 → x' ^ 2 + t * x' * y' + n * y' ^ 2 = 0 →
    x * x' - n * y * y' = 0 ∧ x * y' + x' * y + t * y * y' = 0 := by
  intro x y x' y' t n
  fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;> fin_cases t <;> fin_cases n <;> decide

/-- **Lemma D at `2`**: products of two elements of `R = ℤ[ω]` with even trace and norm lie in `2R`. -/
theorem two_mul_cond (x y x' y' t n : ℤ) (h1 : (2 : ℤ) ∣ 2 * x + t * y)
    (h2 : (2 : ℤ) ∣ x ^ 2 + t * x * y + n * y ^ 2) (h3 : (2 : ℤ) ∣ 2 * x' + t * y')
    (h4 : (2 : ℤ) ∣ x' ^ 2 + t * x' * y' + n * y' ^ 2) :
    (2 : ℤ) ∣ x * x' - n * y * y' ∧ (2 : ℤ) ∣ x * y' + x' * y + t * y * y' := by
  have key : ∀ w : ℤ, (2 : ℤ) ∣ w ↔ ((w : ZMod 2) = 0) := fun w =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd w 2).symm
  simp only [key] at *
  push_cast at *
  exact zmod2_aux _ _ _ _ _ _ h1 h2 h3 h4

end NT

end EichlerBound
