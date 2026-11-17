import ZInQKernel.Contrib.OneProof.HfxProof.Order

/-!
# hfx-proof: the 2-adic obstruction, general form

Task hfx-proof. Generalizes t21-proof's `two_adic_step` (the class of `1`, `ω² = ω − 1`): if
`q n β' (c u) = β e` in `ℍ[ℚ_2]` with `n` integral of norm `2^k`, `β, β'` integral of odd norm,
`u ∈ R_2^×` (`R_2 = ℤ_2 + ℤ_2 ω + 4O_{B,2}`), then
* (`e = 1`) `μ β ≡ β' (X + Y ω) (mod 4)` for a Hurwitz unit `μ` (`two_adic_b1`);
* (`nrd e = 2 · odd`) `(1 − i) β e ≡ 2 μ β' (X + Y ω) (mod 8)` (`two_adic_b2`).
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.T21Proof
open scoped Quaternion

/-- Reduction `ℤ_2 → ℤ/8`. -/
def red8 : ℤ_[2] →+* ZMod 8 := PadicInt.toZModPow 3

/-- `ℤ → ℤ_2`. -/
abbrev cZ : ℤ →+* ℤ_[2] := Int.castRingHom ℤ_[2]

theorem red4_four : red4 (4 : ℤ_[2]) = 0 := by rw [map_ofNat]; rfl

theorem red8_eight : red8 (8 : ℤ_[2]) = 0 := by rw [map_ofNat]; rfl

theorem red4_cZ (m : ℤ) : red4 (cZ m) = (m : ZMod 4) := by simp

theorem red8_cZ (m : ℤ) : red8 (cZ m) = (m : ZMod 8) := by simp

theorem mapH_coe_injective : Function.Injective (mapH (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])) := by
  intro a b h
  simp only [mapH, H4.mk.injEq] at h
  ext
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem coe_comp_cZ : (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]).comp cZ = Int.castRingHom ℚ_[2] :=
  RingHom.ext_int _ _

theorem mapH_mapH {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (x : H4 A) : mapH g (mapH f x) = mapH (g.comp f) x := rfl

/-- Coordinates of an element of `R_2` over `ℤ_2`. -/
theorem inR_coords {u : ℍ[ℚ_[2]]} {ωc : H4 ℤ} (hR : InR (hurZ ωc) u) :
    ∃ X Z : ℤ_[2], ∃ A : H4 ℤ_[2], hc u = mapH PadicInt.Coe.ringHom
      ⟨X + Z * cZ ωc.a0 + 4 * A.a0, Z * cZ ωc.a1 + 4 * A.a1, Z * cZ ωc.a2 + 4 * A.a2,
        Z * cZ ωc.a3 + 4 * A.a3⟩ := by
  obtain ⟨x, z, hx, hz, a, ha, rfl⟩ := hR
  obtain ⟨h0, h1, h2, h3⟩ := ha
  refine ⟨⟨x, hx⟩, ⟨z, hz⟩, ⟨⟨_, mem_Zp.mp h0⟩, ⟨_, mem_Zp.mp h1⟩, ⟨_, mem_Zp.mp h2⟩,
    ⟨_, mem_Zp.mp h3⟩⟩, ?_⟩
  rw [hc_add, hc_add, hc_smul, hc_smul, hc_smul, hc_one, hc_hurZ]
  ext <;> simp [mapH] <;> rfl

theorem norm_odd_int {m : ℤ} (h : Odd m) : ‖((m : ℤ) : ℚ_[2])‖ = 1 := by
  refine le_antisymm (Padic.norm_int_le_one _) (not_lt.mp fun hlt => ?_)
  have := Padic.norm_intCast_lt_one_iff.mp hlt
  obtain ⟨r, hr⟩ := h
  omega

theorem norm_two_pow (k : ℕ) : ‖((2 ^ k : ℤ) : ℚ_[2])‖ = (2 : ℝ) ^ (-(k : ℤ)) := by
  push_cast
  have := Padic.norm_p_pow (p := 2) k
  exact_mod_cast this

/-- The valuation bookkeeping: `‖d‖² 2^{-k} = 2^{-b}` (`b ≤ 1`) forces `k = 2m + b`, `‖d 2^m‖ = 1`. -/
theorem val_bookkeeping {d : ℚ_[2]} (hd : d ≠ 0) {k b : ℕ} (hb : b ≤ 1)
    (h : ‖d‖ ^ 2 * (2 : ℝ) ^ (-(k : ℤ)) = (2 : ℝ) ^ (-(b : ℤ))) :
    ∃ m : ℕ, k = 2 * m + b ∧ ‖d * ((2 ^ m : ℤ) : ℚ_[2])‖ = 1 := by
  rw [Padic.norm_eq_zpow_neg_valuation hd, ← zpow_natCast, ← zpow_mul, Nat.cast_ofNat,
    ← zpow_add₀ (by norm_num)] at h
  have hexp : -d.valuation * ((2 : ℕ) : ℤ) + -(k : ℤ) = -(b : ℤ) := by
    have := (zpow_right_inj₀ (a := (2 : ℝ)) (by norm_num) (by norm_num)).mp h
    exact_mod_cast this
  push_cast at hexp
  set m : ℕ := (-d.valuation).toNat with hm
  have hmv : (m : ℤ) = -d.valuation := Int.toNat_of_nonneg (by omega)
  refine ⟨m, by omega, ?_⟩
  rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hd, norm_two_pow, hmv]
  push_cast
  rw [← zpow_add₀ (by norm_num)]
  simp

/-- **The 2-adic step, `e = 1`.** -/
theorem two_adic_b1 (q : ℚ) (hq : q ≠ 0) (nn : H4 ℤ) (k : ℕ) (hk : nrdH nn = 2 ^ k)
    (β β' ωc : H4 ℤ) (hβ : Odd (nrdH β)) (hβ' : Odd (nrdH β')) (c : ℚ_[2]) (hc0 : c ≠ 0)
    (u : ℍ[ℚ_[2]]) (hnu : ‖Quaternion.normSq u‖ = 1) (hR : InR (hurZ ωc) u)
    (heq : qp 2 (q • hurZ nn) * hurZ β' * (c • u) = hurZ β) :
    ∃ μ ∈ unitList, ∃ X Y : ZMod 4, mapH (Int.castRingHom (ZMod 4)) (mulH μ β) =
      mulH (mapH (Int.castRingHom (ZMod 4)) β')
        ⟨X + Y * (ωc.a0 : ZMod 4), Y * (ωc.a1 : ZMod 4), Y * (ωc.a2 : ZMod 4), Y * (ωc.a3 : ZMod 4)⟩ := by
  rw [qp_smul, qp_hurZ, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul] at heq
  set d : ℚ_[2] := (q : ℚ_[2]) * c with hd
  have hd0 : d ≠ 0 := mul_ne_zero (by exact_mod_cast hq) hc0
  have hN := congrArg Quaternion.normSq heq
  rw [Quaternion.normSq_smul, map_mul, map_mul, normSq_hurZ, normSq_hurZ, normSq_hurZ, hk] at hN
  have hnorm := congrArg norm hN
  rw [norm_odd_int hβ, norm_mul, norm_mul, norm_mul, norm_odd_int hβ', hnu, mul_one, mul_one,
    norm_pow, norm_two_pow, mul_comm] at hnorm
  obtain ⟨m, hkm, hε⟩ := val_bookkeeping (b := 0) hd0 (le_of_lt Nat.zero_lt_one)
    (by rw [mul_comm]; simpa using hnorm)
  have hk4 : nrdH nn = 4 ^ m := by rw [hk, hkm, add_zero, pow_mul]; norm_num
  obtain ⟨μ₀, hμ₀, rfl⟩ := eq_smul_unit_of_nrdH m nn hk4
  rw [hurZ_smulH, smul_mul_assoc, smul_mul_assoc, smul_smul] at heq
  set ε : ℚ_[2] := d * ((2 ^ m : ℤ) : ℚ_[2]) with hεdef
  have hεn : ‖ε‖ = 1 := hε
  have heq' : hurZ μ₀ * hurZ β' * (ε • u) = hurZ β := by
    rw [← heq, mul_smul_comm, hεdef]
  have hstar : (hurZ (starH μ₀) : ℍ[ℚ_[2]]) * hurZ μ₀ = 1 := by
    rw [← star_hurZ, Quaternion.star_mul_self, normSq_hurZ, hμ₀]; simp
  have h3 : hurZ β' * (ε • u) = (hurZ (mulH (starH μ₀) β) : ℍ[ℚ_[2]]) := by
    rw [hurZ_mulH, ← heq', ← mul_assoc, ← mul_assoc, hstar, one_mul]
  obtain ⟨X, Z, A, hU⟩ := inR_coords (InR.smul (le_of_eq hεn) hR)
  have h4 := congrArg hc h3
  rw [hc_mul, hc_hurZ, hc_hurZ, hU, ← coe_comp_cZ, ← mapH_mapH, ← mapH_mapH, ← mapH_mulH] at h4
  have h5 := congrArg (mapH red4) (mapH_coe_injective h4)
  rw [mapH_mulH, mapH_mapH, mapH_mapH] at h5
  have hrc : red4.comp cZ = Int.castRingHom (ZMod 4) := RingHom.ext_int _ _
  rw [hrc] at h5
  refine ⟨starH μ₀, mem_unitList (by rw [nrdH_starH, hμ₀]), red4 X, red4 Z, h5.symm.trans ?_⟩
  congr 1
  simp only [mapH, map_add, map_mul, red4_four, zero_mul, add_zero, red4_cZ]

/-- `1 − i` in Hurwitz coordinates. -/
def oneMI : H4 ℤ := ⟨1, -1, 0, 0⟩

theorem hurZ_oneMI_mul_oneI {R : Type*} [Field R] [CharZero R] :
    (hurZ oneMI : ℍ[R]) * hurZ oneI = (2 : R) • 1 := by
  apply hc_injective
  rw [hc_mul_hurZ, hc_smul, hc_one]
  ext <;> simp [mapH, mulH, oneMI, oneI] <;> norm_num

theorem red8_two_mul (X Z : ℤ_[2]) (A : ℤ_[2]) (w : ℤ) :
    red8 (2 * (X + Z * cZ w + 4 * A)) = 2 * red8 X + 2 * red8 Z * (w : ZMod 8) := by
  have : (2 : ℤ_[2]) * (X + Z * cZ w + 4 * A) = 2 * X + 2 * Z * cZ w + 8 * A := by ring
  rw [this, map_add, map_add, map_mul, map_mul, map_mul, map_mul, red8_eight, red8_cZ, zero_mul,
    add_zero, map_ofNat]

theorem red8_two_mul' (Z : ℤ_[2]) (A : ℤ_[2]) (w : ℤ) :
    red8 (2 * (Z * cZ w + 4 * A)) = 2 * red8 Z * (w : ZMod 8) := by
  have := red8_two_mul 0 Z A w
  rw [zero_add, map_zero, mul_zero, zero_add] at this
  exact this

/-- **The 2-adic step, `nrd e = 2 · odd`.** -/
theorem two_adic_b2 (q : ℚ) (hq : q ≠ 0) (nn : H4 ℤ) (k : ℕ) (hk : nrdH nn = 2 ^ k)
    (β β' ωc e : H4 ℤ) (hβ : Odd (nrdH β)) (hβ' : Odd (nrdH β')) (o : ℤ) (ho : Odd o)
    (he : nrdH e = 2 * o) (c : ℚ_[2]) (hc0 : c ≠ 0)
    (u : ℍ[ℚ_[2]]) (hnu : ‖Quaternion.normSq u‖ = 1) (hR : InR (hurZ ωc) u)
    (heq : qp 2 (q • hurZ nn) * hurZ β' * (c • u) = hurZ β * hurZ e) :
    ∃ μ ∈ unitList, ∃ X Y : ZMod 8, mapH (Int.castRingHom (ZMod 8)) (mulH oneMI (mulH β e)) =
      mulH (mapH (Int.castRingHom (ZMod 8)) (mulH μ β'))
        ⟨2 * X + 2 * Y * (ωc.a0 : ZMod 8), 2 * Y * (ωc.a1 : ZMod 8), 2 * Y * (ωc.a2 : ZMod 8),
          2 * Y * (ωc.a3 : ZMod 8)⟩ := by
  rw [qp_smul, qp_hurZ, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul] at heq
  set d : ℚ_[2] := (q : ℚ_[2]) * c with hd
  have hd0 : d ≠ 0 := mul_ne_zero (by exact_mod_cast hq) hc0
  have hN := congrArg Quaternion.normSq heq
  rw [Quaternion.normSq_smul, map_mul, map_mul, map_mul, normSq_hurZ, normSq_hurZ, normSq_hurZ,
    normSq_hurZ, hk, he] at hN
  have hnorm := congrArg norm hN
  have h2 : ‖((2 * o : ℤ) : ℚ_[2])‖ = (2 : ℝ) ^ (-(1 : ℤ)) := by
    push_cast; rw [norm_mul]
    rw [show ‖(o : ℚ_[2])‖ = 1 from norm_odd_int ho, mul_one]
    rw [show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by norm_num, Padic.norm_p]; norm_num
  simp only [norm_mul, norm_pow] at hnorm
  rw [h2, norm_odd_int hβ, norm_odd_int hβ', hnu, norm_two_pow, mul_one, one_mul] at hnorm
  obtain ⟨m, hkm, hε⟩ := val_bookkeeping (b := 1) hd0 le_rfl (by simpa [mul_comm] using hnorm)
  have hev : Even (nrdH nn) := ⟨2 ^ (2 * m), by rw [hk, hkm]; ring⟩
  obtain ⟨nn', rfl⟩ := exists_oneI_mul hev
  have hk4 : nrdH nn' = 4 ^ m := by
    rw [nrdH_mulH, show nrdH oneI = 2 from rfl, hkm] at hk
    have : (2 : ℤ) * nrdH nn' = 2 * 4 ^ m := by rw [hk, pow_succ, pow_mul]; norm_num; ring
    linarith
  obtain ⟨μ₀, hμ₀, rfl⟩ := eq_smul_unit_of_nrdH m nn' hk4
  rw [hurZ_mulH, hurZ_smulH] at heq
  set ε : ℚ_[2] := d * ((2 ^ m : ℤ) : ℚ_[2]) with hεdef
  have hεn : ‖ε‖ = 1 := hε
  have heq' : hurZ oneI * (hurZ μ₀ * hurZ β' * (ε • u)) = hurZ (mulH β e) := by
    rw [hurZ_mulH, ← heq, hεdef]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
  have h3 : (2 : ℚ_[2]) • (hurZ μ₀ * hurZ β' * (ε • u)) = (hurZ (mulH oneMI (mulH β e)) : ℍ[ℚ_[2]]) := by
    rw [hurZ_mulH, ← heq', ← mul_assoc, hurZ_oneMI_mul_oneI, smul_mul_assoc, one_mul]
  obtain ⟨X, Z, A, hU⟩ := inR_coords (InR.smul (le_of_eq hεn) hR)
  have h4 := congrArg hc h3
  rw [hc_smul, hc_mul, hc_mul, hc_hurZ, hc_hurZ, hc_hurZ, hU] at h4
  have h4' : mapH PadicInt.Coe.ringHom (mulH (mapH cZ (mulH μ₀ β'))
      ⟨2 * (X + Z * cZ ωc.a0 + 4 * A.a0), 2 * (Z * cZ ωc.a1 + 4 * A.a1), 2 * (Z * cZ ωc.a2 + 4 * A.a2),
        2 * (Z * cZ ωc.a3 + 4 * A.a3)⟩) = mapH PadicInt.Coe.ringHom (mapH cZ (mulH oneMI (mulH β e))) := by
    rw [mapH_mapH, coe_comp_cZ, ← h4]
    ext <;> simp only [mapH, mulH, map_add, map_sub, map_mul, map_neg, map_ofNat, map_intCast,
      eq_intCast] <;> ring
  have h5 := congrArg (mapH red8) (mapH_coe_injective h4')
  rw [mapH_mulH, mapH_mapH, mapH_mapH] at h5
  have hrc : red8.comp cZ = Int.castRingHom (ZMod 8) := RingHom.ext_int _ _
  rw [hrc] at h5
  refine ⟨μ₀, mem_unitList hμ₀, red8 X, red8 Z, h5.symm.trans ?_⟩
  congr 1
  simp only [mapH, red8_two_mul, red8_two_mul']

end ZInQ.Contrib.HfxProof
