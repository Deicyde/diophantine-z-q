import ZInQKernel.Contrib.OneProof.T21Proof.LocalPred

/-!
# t21-proof: the global step and the 2-adic obstruction

Task t21-proof.
* `global_step`: a nonzero `γ ∈ B = ℍ[ℚ]` lying in `ℚ_p^× O_{B,p}^×` at every odd prime `p` is
  `q · n` with `n` an integral Hurwitz element of norm `2^k`.
* `two_adic_step`: if moreover `γ⁻¹ β ∈ ℚ_2^× R_2^×` (`R_2 = ℤ_2 + ℤ_2 ω + 4O_{B,2}`) for an
  integral `β` of odd norm, then `μ β ≡ X + Y ω (mod 4O_B)` for a unit `μ` of `O_B`.
* `unitList`: the 24 units of the Hurwitz order (every integral element of norm `1` is in it).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open scoped Quaternion

/-! ## `p`-adic norms -/

theorem norm_le_inv_of_lt_one {p : ℕ} [hp : Fact p.Prime] {x : ℚ_[p]} (h : ‖x‖ < 1) :
    ‖x‖ ≤ (p : ℝ)⁻¹ := by
  by_cases hx : x = 0
  · rw [hx, norm_zero]; positivity
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [Padic.norm_eq_zpow_neg_valuation hx] at h ⊢
  have hv : 1 ≤ x.valuation := by
    by_contra hv
    push_neg at hv
    have : (1 : ℝ) ≤ (p : ℝ) ^ (-x.valuation) := one_le_zpow₀ hp1.le (by omega)
    linarith
  calc (p : ℝ) ^ (-x.valuation) ≤ (p : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hp1.le (by omega)
    _ = (p : ℝ)⁻¹ := zpow_neg_one _

/-- The cast of `hur` of an integer vector. -/
def hurZ {R : Type*} [Field R] [CharZero R] (n : H4 ℤ) : ℍ[R] := hur (mapH (Int.castRingHom R) n)

theorem qp_hurZ {p : ℕ} [Fact p.Prime] (n : H4 ℤ) : qp p (hurZ n) = hurZ n := by
  apply hc_injective
  rw [qp, hc_qmap, hurZ, hurZ, hc_hur, hc_hur]
  ext <;> simp [mapH]

theorem normSq_hurZ {R : Type*} [Field R] [CharZero R] (n : H4 ℤ) :
    Quaternion.normSq (hurZ n : ℍ[R]) = ((nrdH n : ℤ) : R) := by
  rw [normSq_eq_nrdH, hurZ, hc_hur, ← map_nrdH]; rfl

theorem nrdH_pos {n : H4 ℤ} (hn : n ≠ ⟨0, 0, 0, 0⟩) : 0 < nrdH n := by
  have h4 : 4 * nrdH n = (2 * n.a0 - n.a3) ^ 2 + (2 * n.a1 + n.a3) ^ 2 + (2 * n.a2 + n.a3) ^ 2 +
      n.a3 ^ 2 := by simp only [nrdH]; ring
  by_contra h
  push_neg at h
  have s0 := sq_nonneg (2 * n.a0 - n.a3)
  have s1 := sq_nonneg (2 * n.a1 + n.a3)
  have s2 := sq_nonneg (2 * n.a2 + n.a3)
  have s3 := sq_nonneg n.a3
  have h0 : n.a3 = 0 := by nlinarith
  have h1 : n.a0 = 0 := by nlinarith
  have h2 : n.a1 = 0 := by nlinarith
  have h3 : n.a2 = 0 := by nlinarith
  exact hn (by ext <;> assumption)

/-! ## A primitive integer vector -/

theorem exists_primitive (γ : ℍ[ℚ]) (hγ : γ ≠ 0) : ∃ (q : ℚ) (n : H4 ℤ), q ≠ 0 ∧
    γ = q • hurZ n ∧ n ≠ ⟨0, 0, 0, 0⟩ ∧
    ∀ d : ℤ, d ∣ n.a0 → d ∣ n.a1 → d ∣ n.a2 → d ∣ n.a3 → IsUnit d := by
  set x := hc γ with hx
  set D : ℕ := x.a0.den * x.a1.den * x.a2.den * x.a3.den with hD
  have hDpos : 0 < D := by positivity
  have hint : ∀ r : ℚ, r.den ∣ D → ∃ m : ℤ, (m : ℚ) = r * D := fun r hr => by
    obtain ⟨e, he⟩ := hr
    refine ⟨r.num * e, ?_⟩
    rw [he]; push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  obtain ⟨m0, e0⟩ := hint x.a0 ⟨x.a1.den * x.a2.den * x.a3.den, by rw [hD]; ring⟩
  obtain ⟨m1, e1⟩ := hint x.a1 ⟨x.a0.den * x.a2.den * x.a3.den, by rw [hD]; ring⟩
  obtain ⟨m2, e2⟩ := hint x.a2 ⟨x.a0.den * x.a1.den * x.a3.den, by rw [hD]; ring⟩
  obtain ⟨m3, e3⟩ := hint x.a3 ⟨x.a0.den * x.a1.den * x.a2.den, by rw [hD]; ring⟩
  set g : ℤ := ((Int.gcd m0 (Int.gcd m1 (Int.gcd m2 m3) : ℤ)) : ℤ) with hg
  have hm_ne : ¬ (m0 = 0 ∧ m1 = 0 ∧ m2 = 0 ∧ m3 = 0) := by
    rintro ⟨h0, h1, h2, h3⟩
    apply hγ
    apply hc_injective
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    rw [h0] at e0; rw [h1] at e1; rw [h2] at e2; rw [h3] at e3
    simp only [Int.cast_zero] at e0 e1 e2 e3
    have : hc (0 : ℍ[ℚ]) = ⟨0, 0, 0, 0⟩ := by ext <;> simp [hc]
    rw [this]
    ext
    · exact (mul_eq_zero.mp e0.symm).resolve_right hD0
    · exact (mul_eq_zero.mp e1.symm).resolve_right hD0
    · exact (mul_eq_zero.mp e2.symm).resolve_right hD0
    · exact (mul_eq_zero.mp e3.symm).resolve_right hD0
  have hg0 : g ≠ 0 := by
    intro h
    rw [hg, Int.natCast_eq_zero, Int.gcd_eq_zero_iff] at h
    obtain ⟨h0, h⟩ := h
    rw [Int.natCast_eq_zero, Int.gcd_eq_zero_iff] at h
    obtain ⟨h1, h⟩ := h
    rw [Int.natCast_eq_zero, Int.gcd_eq_zero_iff] at h
    exact hm_ne ⟨h0, h1, h.1, h.2⟩
  have d0 : g ∣ m0 := Int.gcd_dvd_left _ _
  have d1 : g ∣ m1 := (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _)
  have d2 : g ∣ m2 := ((Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)).trans
    (Int.gcd_dvd_left _ _)
  have d3 : g ∣ m3 := ((Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)).trans
    (Int.gcd_dvd_right _ _)
  clear_value g
  obtain ⟨n0, rfl⟩ := d0
  obtain ⟨n1, rfl⟩ := d1
  obtain ⟨n2, rfl⟩ := d2
  obtain ⟨n3, rfl⟩ := d3
  refine ⟨(g : ℚ) / D, ⟨n0, n1, n2, n3⟩, ?_, ?_, ?_, ?_⟩
  · have : (g : ℚ) ≠ 0 := by exact_mod_cast hg0
    exact div_ne_zero this (by exact_mod_cast hDpos.ne')
  · apply hc_injective
    rw [hc_smul, hurZ, hc_hur]
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    push_cast at e0 e1 e2 e3
    ext <;> simp only [mapH, eq_intCast]
    · rw [← hx]; field_simp; linarith
    · rw [← hx]; field_simp; linarith
    · rw [← hx]; field_simp; linarith
    · rw [← hx]; field_simp; linarith
  · intro h
    simp only [H4.mk.injEq] at h
    apply hm_ne
    simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · intro d h0 h1 h2 h3
    have hdg : g * d ∣ g := by
      have := Int.dvd_coe_gcd (mul_dvd_mul_left g h0) (Int.dvd_coe_gcd (mul_dvd_mul_left g h1)
        (Int.dvd_coe_gcd (mul_dvd_mul_left g h2) (mul_dvd_mul_left g h3)))
      rw [← hg] at this
      exact this
    obtain ⟨e, he⟩ := hdg
    have hde : d * e = 1 := by
      have : g * 1 = g * (d * e) := by rw [mul_one]; nth_rewrite 1 [he]; ring
      exact (mul_left_cancel₀ hg0 this).symm
    exact ⟨⟨d, e, hde, by rw [mul_comm]; exact hde⟩, rfl⟩

theorem qp_smul {p : ℕ} [Fact p.Prime] (q : ℚ) (y : ℍ[ℚ]) :
    qp p (q • y) = (q : ℚ_[p]) • qp p y := by
  ext <;> simp [qp]

theorem norm_intCast_le_one {p : ℕ} [Fact p.Prime] (m : ℤ) : ‖(m : ℚ_[p])‖ ≤ 1 :=
  Padic.norm_int_le_one m

/-! ## The global step -/

/-- **Global step.** A nonzero `γ ∈ ℍ[ℚ]` that lies in `ℚ_p^× O_{B,p}^×` at every odd prime is
`q · n` with `n` an integral Hurwitz element of norm a power of `2`. -/
theorem global_step (γ : ℍ[ℚ]) (hγ : γ ≠ 0)
    (h : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → LocOK (qp p γ)) :
    ∃ (q : ℚ) (n : H4 ℤ) (k : ℕ), q ≠ 0 ∧ γ = q • hurZ n ∧ nrdH n = 2 ^ k := by
  obtain ⟨q, n, hq, rfl, hn0, hprim⟩ := exists_primitive γ hγ
  have hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ nrdH n := by
    intro p hpp hp2 hdvd
    have : Fact p.Prime := ⟨hpp⟩
    obtain ⟨c, hc0, u, hcu, hu, hnu⟩ := h p hp2
    rw [qp_smul, qp_hurZ] at hcu
    have hq' : (q : ℚ_[p]) ≠ 0 := by exact_mod_cast hq
    set c' := (q : ℚ_[p])⁻¹ * c with hc'
    have hcu' : (hurZ n : ℍ[ℚ_[p]]) = c' • u := by
      rw [hc', mul_smul, ← hcu, smul_smul, inv_mul_cancel₀ hq', one_smul]
    -- the norm
    have hN : ((nrdH n : ℤ) : ℚ_[p]) = c' ^ 2 * Quaternion.normSq u := by
      rw [← normSq_hurZ, hcu', Quaternion.normSq_smul]
    have hlt : ‖((nrdH n : ℤ) : ℚ_[p])‖ < 1 := Padic.norm_intCast_lt_one_iff.mpr hdvd
    rw [hN, norm_mul, hnu, mul_one, norm_pow] at hlt
    have hc1 : ‖c'‖ < 1 := by nlinarith [norm_nonneg c']
    -- every coordinate is divisible by `p`
    have hcoord := congrArg hc hcu'
    rw [hurZ, hc_hur, hc_smul] at hcoord
    obtain ⟨u0, u1, u2, u3⟩ := hu
    have key : ∀ (m : ℤ) (y : ℚ_[p]), y ∈ Zp p → (m : ℚ_[p]) = c' * y → (p : ℤ) ∣ m := by
      intro m y hy hm
      apply Padic.norm_intCast_lt_one_iff.mp
      rw [hm, norm_mul]
      calc ‖c'‖ * ‖y‖ ≤ ‖c'‖ * 1 := by gcongr; exact hy
        _ < 1 := by rw [mul_one]; exact hc1
    simp only [mapH, H4.mk.injEq, eq_intCast] at hcoord
    have := hprim p (key _ _ u0 hcoord.1) (key _ _ u1 hcoord.2.1) (key _ _ u2 hcoord.2.2.1)
      (key _ _ u3 hcoord.2.2.2)
    rw [Int.isUnit_iff] at this
    have h2 := hpp.two_le
    omega
  have hpos := nrdH_pos hn0
  set N := (nrdH n).toNat with hNdef
  have hNn : (N : ℤ) = nrdH n := Int.toNat_of_nonneg hpos.le
  have hN0 : N ≠ 0 := by omega
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hN0 (p := 2) (fun {d} hd hdN => by
    by_contra hd2
    exact hodd d hd hd2 (by rw [← hNn]; exact_mod_cast hdN))
  refine ⟨q, n, N.primeFactorsList.length, hq, rfl, ?_⟩
  rw [← hNn]
  exact_mod_cast hpow

/-! ## The 2-adic step -/

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem nrdH_starH {A : Type*} [CommRing A] (a : H4 A) : nrdH (starH a) = nrdH a := by
  simp only [nrdH, starH]; ring

theorem star_hurZ {R : Type*} [Field R] [CharZero R] (n : H4 ℤ) :
    star (hurZ n : ℍ[R]) = hurZ (starH n) := by
  apply hc_injective
  rw [hc_star, hurZ, hurZ, hc_hur, hc_hur, mapH_starH]

theorem hurZ_smulH {R : Type*} [Field R] [CharZero R] (m : ℤ) (n : H4 ℤ) :
    (hurZ (smulH m n) : ℍ[R]) = (m : R) • hurZ n := by
  apply hc_injective
  rw [hc_smul, hurZ, hurZ, hc_hur, hc_hur]
  ext <;> simp [mapH, smulH]

theorem hc_hurZ {R : Type*} [Field R] [CharZero R] (n : H4 ℤ) :
    hc (hurZ n : ℍ[R]) = mapH (Int.castRingHom R) n := by
  rw [hurZ, hc_hur]

theorem hc_mul_hurZ {R : Type*} [Field R] [CharZero R] (m n : H4 ℤ) :
    hc ((hurZ m : ℍ[R]) * hurZ n) = mapH (Int.castRingHom R) (mulH m n) := by
  rw [hc_mul, hc_hurZ, hc_hurZ, mapH_mulH]

/-- Reduction `ℤ_2 → ℤ/4`. -/
def red4 : ℤ_[2] →+* ZMod 4 := PadicInt.toZModPow 2

theorem red4_eq_zero_of_norm {x : ℤ_[2]} (h : ‖x‖ ≤ 1 / 4) : red4 x = 0 := by
  have hx : ‖x‖ ≤ ((2 : ℕ) : ℝ) ^ (-(2 : ℕ) : ℤ) := by norm_num; linarith
  rw [PadicInt.norm_le_pow_iff_mem_span_pow] at hx
  rw [red4, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
  exact hx

/-- **The 2-adic step.** -/
theorem two_adic_step (q : ℚ) (hq : q ≠ 0) (n : H4 ℤ) (k : ℕ) (hk : nrdH n = 2 ^ k)
    (β : H4 ℤ) (hβ : Odd (nrdH β)) (ωc : H4 ℤ) (c : ℚ_[2]) (hc0 : c ≠ 0) (u : ℍ[ℚ_[2]])
    (hu : IsHur (Zp 2) u) (hnu : ‖Quaternion.normSq u‖ = 1) (hR : InR (hurZ ωc) u)
    (heq : qp 2 (q • hurZ n) * (c • u) = hurZ β) :
    ∃ μ : H4 ℤ, nrdH μ = 1 ∧ ∃ X Y : ZMod 4, mapH (Int.castRingHom (ZMod 4)) (mulH μ β) =
      ⟨X + Y * (ωc.a0 : ZMod 4), Y * (ωc.a1 : ZMod 4), Y * (ωc.a2 : ZMod 4),
        Y * (ωc.a3 : ZMod 4)⟩ := by
  rw [qp_smul, qp_hurZ, smul_mul_smul] at heq
  set d : ℚ_[2] := (q : ℚ_[2]) * c with hd
  have hq' : (q : ℚ_[2]) ≠ 0 := by exact_mod_cast hq
  have hd0 : d ≠ 0 := mul_ne_zero hq' hc0
  -- norms
  have hN := congrArg Quaternion.normSq heq
  rw [Quaternion.normSq_smul, map_mul, normSq_hurZ, normSq_hurZ, hk] at hN
  have hβn : ‖((nrdH β : ℤ) : ℚ_[2])‖ = 1 := by
    refine le_antisymm (Padic.norm_int_le_one _) (not_lt.mp fun hlt => ?_)
    have := Padic.norm_intCast_lt_one_iff.mp hlt
    obtain ⟨r, hr⟩ := hβ
    omega
  have hnorm := congrArg norm hN
  rw [hβn, norm_mul, norm_mul, hnu, mul_one, norm_pow] at hnorm
  have h2k : ‖((2 ^ k : ℤ) : ℚ_[2])‖ = (2 : ℝ) ^ (-(k : ℤ)) := by
    push_cast
    have := Padic.norm_p_pow (p := 2) k
    exact_mod_cast this
  rw [h2k, Padic.norm_eq_zpow_neg_valuation hd0, ← zpow_natCast, ← zpow_mul, Nat.cast_ofNat,
    ← zpow_add₀ (by norm_num)] at hnorm
  have hexp : -d.valuation * ((2 : ℕ) : ℤ) + -(k : ℤ) = 0 := by
    have := (zpow_right_inj₀ (a := (2 : ℝ)) (by norm_num) (by norm_num)).mp (hnorm.trans (zpow_zero _).symm)
    exact_mod_cast this
  set m : ℕ := (-d.valuation).toNat with hm
  have hmv : (m : ℤ) = -d.valuation := Int.toNat_of_nonneg (by omega)
  have hkm : k = 2 * m := by omega
  have hk4 : nrdH n = 4 ^ m := by rw [hk, hkm, pow_mul]; norm_num
  obtain ⟨μ₀, hμ₀, rfl⟩ := eq_smul_unit_of_nrdH m n hk4
  rw [hurZ_smulH, Algebra.smul_mul_assoc, smul_smul] at heq
  set ε : ℚ_[2] := d * ((2 ^ m : ℤ) : ℚ_[2]) with hε
  have hεn : ‖ε‖ = 1 := by
    rw [hε, norm_mul, Padic.norm_eq_zpow_neg_valuation hd0]
    push_cast
    rw [show ((2 : ℚ_[2]) ^ m) = ((2 : ℕ) : ℚ_[2]) ^ m by norm_num, Padic.norm_p_pow,
      Nat.cast_ofNat, ← zpow_add₀ (by norm_num), hmv]
    simp
  -- multiply by the conjugate of `μ₀`
  have hstar : (hurZ (starH μ₀) : ℍ[ℚ_[2]]) * hurZ μ₀ = 1 := by
    rw [← star_hurZ, Quaternion.star_mul_self, normSq_hurZ, hμ₀]; simp
  have h3 : (hurZ (starH μ₀) : ℍ[ℚ_[2]]) * hurZ β = ε • u := by
    rw [← heq, Algebra.mul_smul_comm, ← mul_assoc, hstar, one_mul]
  have h4 := congrArg hc h3
  rw [hc_mul_hurZ, hc_smul] at h4
  obtain ⟨x, z, hx, hz, a, ha, rfl⟩ := hR
  have hcu : hc (x • (1 : ℍ[ℚ_[2]]) + z • hurZ ωc + (4 : ℚ_[2]) • a) =
      ⟨x + z * ωc.a0 + 4 * (hc a).a0, z * ωc.a1 + 4 * (hc a).a1, z * ωc.a2 + 4 * (hc a).a2,
        z * ωc.a3 + 4 * (hc a).a3⟩ := by
    rw [hc_add, hc_add, hc_smul, hc_smul, hc_smul, hc_one, hc_hurZ]
    ext <;> simp [mapH]
  rw [hcu] at h4
  obtain ⟨a0, a1, a2, a3⟩ := ha
  have hX : ‖ε * x‖ ≤ 1 := by rw [norm_mul, hεn, one_mul]; exact hx
  have hZ : ‖ε * z‖ ≤ 1 := by rw [norm_mul, hεn, one_mul]; exact hz
  have hA : ∀ y : ℚ_[2], y ∈ Zp 2 → ‖ε * y‖ ≤ 1 := fun y hy => by
    rw [norm_mul, hεn, one_mul]; exact hy
  let X : ℤ_[2] := ⟨ε * x, hX⟩
  let Z : ℤ_[2] := ⟨ε * z, hZ⟩
  have red_eq : ∀ (r w : ℤ) (X' Z' A : ℤ_[2]),
      (r : ℚ_[2]) = (X' : ℚ_[2]) + (Z' : ℚ_[2]) * w + 4 * (A : ℚ_[2]) →
      ((r : ZMod 4)) = red4 X' + red4 Z' * (w : ZMod 4) := by
    intro r w X' Z' A h
    have h' : (r : ℤ_[2]) = X' + Z' * w + 4 * A := PadicInt.ext (by push_cast; exact h)
    have h'' := congrArg red4 h'
    rw [map_intCast, map_add, map_add, map_mul, map_mul, map_intCast] at h''
    rw [h'']
    have : red4 4 = 0 := by rw [map_ofNat]; rfl
    rw [this, zero_mul, add_zero]
  refine ⟨starH μ₀, by rw [nrdH_starH, hμ₀], red4 X, red4 Z, ?_⟩
  simp only [mapH, H4.mk.injEq] at h4 ⊢
  obtain ⟨e0, e1, e2, e3⟩ := h4
  simp only [eq_intCast] at e0 e1 e2 e3 ⊢
  refine ⟨red_eq _ _ X Z ⟨ε * (hc a).a0, (hA _ a0)⟩ ?_,
    ?_, ?_, ?_⟩
  · rw [e0]; simp only [X, Z]; ring
  · have := red_eq _ (ωc.a1) 0 Z ⟨ε * (hc a).a1, (hA _ a1)⟩
      (by rw [e1]; simp only [Z]; push_cast; ring)
    rw [this, map_zero, zero_add]
  · have := red_eq _ (ωc.a2) 0 Z ⟨ε * (hc a).a2, (hA _ a2)⟩
      (by rw [e2]; simp only [Z]; push_cast; ring)
    rw [this, map_zero, zero_add]
  · have := red_eq _ (ωc.a3) 0 Z ⟨ε * (hc a).a3, (hA _ a3)⟩
      (by rw [e3]; simp only [Z]; push_cast; ring)
    rw [this, map_zero, zero_add]

end ZInQ.Contrib.T21Proof
