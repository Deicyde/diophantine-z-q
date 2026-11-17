import ZInQKernel.Contrib.OneProof.HfxProof.Case3

/-!
# hfx-proof: the local condition at `2` for `n ≡ 1 (mod 8)` (ramified `K_2`)

Task hfx-proof. Here `ω = τ(√−n)` (`ω² = −n`) and `K_2 = ℚ_2(ω)` is ramified with uniformizer
`ϖ = 1 + ω` (`nrd ϖ = 1 + n`, of valuation one). `K_2^× = ℚ_2^× R_2^× ∪ ℚ_2^× R_2^× ϖ⁻¹`, where
`R_2 = ℤ_2 + ℤ_2ω + 4O_{B,2}`; the condition `C1` (`y ∈ ℚ_2^× R_2^×` or `yϖ ∈ ℚ_2^× R_2^×`) is a group
because conjugation by `ϖ` preserves `O_{B,2}` (`isHur_conj`: `ϖ̄ a ϖ ∈ 2O_{B,2}`, checked mod 2) and
`ϖ² ∈ ℚ_2^× R_2^×`.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

/-- Mod 2: an element of even norm `P` has `P̄ A P ≡ 0`. -/
theorem conj_mod_two : ∀ p0 p1 p2 p3 a0 a1 a2 a3 : ZMod 2, nrdH (⟨p0, p1, p2, p3⟩ : H4 (ZMod 2)) = 0 →
    mulH (mulH (starH ⟨p0, p1, p2, p3⟩) ⟨a0, a1, a2, a3⟩) ⟨p0, p1, p2, p3⟩ = (⟨0, 0, 0, 0⟩ : H4 (ZMod 2)) := by
  decide

theorem coords_Z2 {z : ℍ[ℚ_[2]]} (hz : IsHur (Zp 2) z) :
    ∃ Z : H4 ℤ_[2], mapH PadicInt.Coe.ringHom Z = hc z := by
  obtain ⟨h0, h1, h2, h3⟩ := hz
  exact ⟨⟨⟨_, mem_Zp.mp h0⟩, ⟨_, mem_Zp.mp h1⟩, ⟨_, mem_Zp.mp h2⟩, ⟨_, mem_Zp.mp h3⟩⟩, rfl⟩

theorem half_mem_of_toZMod {x : ℤ_[2]} (h : PadicInt.toZMod x = 0) :
    ((1 / 2 : ℚ) : ℚ_[2]) * (x : ℚ_[2]) ∈ Zp 2 := by
  have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]; exact h
  have hlt : ‖(x : ℚ_[2])‖ < 1 := by
    rw [← PadicInt.norm_def]; exact PadicInt.mem_nonunits.mp hm
  have hle := norm_le_inv_of_lt_one hlt
  rw [mem_Zp, norm_mul]
  have : ‖((1 / 2 : ℚ) : ℚ_[2])‖ = 2 := by
    push_cast; rw [norm_div, norm_one, show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by norm_num, Padic.norm_p]
    norm_num
  rw [this]; push_cast at hle; linarith

/-- **`ϖ̄ a ϖ ∈ 2O_{B,2}`** for `ϖ` of even norm. -/
theorem isHur_conj {ϖ a : ℍ[ℚ_[2]]} (hϖ : IsHur (Zp 2) ϖ) (hn : ‖Quaternion.normSq ϖ‖ < 1)
    (ha : IsHur (Zp 2) a) : IsHur (Zp 2) (((1 / 2 : ℚ) : ℚ_[2]) • (star ϖ * a * ϖ)) := by
  obtain ⟨Pz, hPz⟩ := coords_Z2 hϖ
  obtain ⟨A, hA⟩ := coords_Z2 ha
  have hnPz : PadicInt.toZMod (nrdH Pz) = 0 := by
    have hm : nrdH Pz ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      refine PadicInt.mem_nonunits.mpr ?_
      rw [PadicInt.norm_def]
      have : ((nrdH Pz : ℤ_[2]) : ℚ_[2]) = Quaternion.normSq ϖ := by
        rw [normSq_eq_nrdH, ← hPz, ← map_nrdH]; rfl
      rw [this]; exact hn
    rw [← PadicInt.ker_toZMod] at hm; exact hm
  have hzero : mapH PadicInt.toZMod (mulH (mulH (starH Pz) A) Pz) = ⟨0, 0, 0, 0⟩ := by
    rw [mapH_mulH, mapH_mulH, mapH_starH]
    rw [map_nrdH] at hnPz
    exact conj_mod_two _ _ _ _ _ _ _ _ hnPz
  have hc' : hc (star ϖ * a * ϖ) = mapH PadicInt.Coe.ringHom (mulH (mulH (starH Pz) A) Pz) := by
    rw [hc_mul, hc_mul, hc_star, ← hPz, ← hA, mapH_mulH, mapH_mulH, mapH_starH]
  simp only [mapH, H4.mk.injEq] at hzero
  simp only [IsHur, hc_smul, hc', mapH]
  exact ⟨half_mem_of_toZMod hzero.1, half_mem_of_toZMod hzero.2.1, half_mem_of_toZMod hzero.2.2.1,
    half_mem_of_toZMod hzero.2.2.2⟩

/-- **Conjugation by `ϖ` preserves `O_{B,2}`** when `‖nrd ϖ‖ = 1/2`. -/
theorem isHur_qinv_conj {ϖ a : ℍ[ℚ_[2]]} (hϖ : IsHur (Zp 2) ϖ) (hn : ‖Quaternion.normSq ϖ‖ = 1 / 2)
    (ha : IsHur (Zp 2) a) : IsHur (Zp 2) (qinv ϖ * a * ϖ) := by
  have h0 : Quaternion.normSq ϖ ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  have e : qinv ϖ * a * ϖ = ((Quaternion.normSq ϖ)⁻¹ * 2) • (((1 / 2 : ℚ) : ℚ_[2]) • (star ϖ * a * ϖ)) := by
    rw [smul_smul, qinv, smul_mul_assoc, smul_mul_assoc]
    congr 1; push_cast; field_simp
  rw [e]
  refine IsHur.smul ?_ (isHur_conj hϖ (by rw [hn]; norm_num) ha)
  rw [mem_Zp, norm_mul, norm_inv, hn, show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by norm_num, Padic.norm_p]
  norm_num

section C1

variable {ω ϖ : ℍ[ℚ_[2]]} {N : ℚ_[2]}

theorem loc2OK_conj (hω : IsHur (Zp 2) ω) (hϖ : IsHur (Zp 2) ϖ) (hn : ‖Quaternion.normSq ϖ‖ = 1 / 2)
    (hcomm : ω * ϖ = ϖ * ω) {z : ℍ[ℚ_[2]]} (hz : Loc2OK ω z) :
    Loc2OK ω (qinv ϖ * z * ϖ) := by
  have h0 : Quaternion.normSq ϖ ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  have hQ1 : qinv ϖ * ϖ = 1 := qinv_mul_self h0
  have hQH : ∀ a, IsHur (Zp 2) a → IsHur (Zp 2) (qinv ϖ * a * ϖ) := fun a ha => isHur_qinv_conj hϖ hn ha
  generalize qinv ϖ = Q at hQ1 hQH ⊢
  obtain ⟨c, hc, u, rfl, hu, hnu, x, y, hx, hy, a, ha, rfl⟩ := hz
  have hqω : Q * ω * ϖ = ω := by rw [mul_assoc, hcomm, ← mul_assoc, hQ1, one_mul]
  have hq1 : Q * (1 : ℍ[ℚ_[2]]) * ϖ = 1 := by rw [mul_one, hQ1]
  have hconj : Q * (x • (1 : ℍ[ℚ_[2]]) + y • ω + (4 : ℚ_[2]) • a) * ϖ =
      x • (1 : ℍ[ℚ_[2]]) + y • ω + (4 : ℚ_[2]) • (Q * a * ϖ) := by
    rw [mul_add, mul_add, add_mul, add_mul, mul_smul_comm, mul_smul_comm, mul_smul_comm,
      smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, hq1, hqω]
  refine ⟨c, hc, Q * (x • (1 : ℍ[ℚ_[2]]) + y • ω + (4 : ℚ_[2]) • a) * ϖ,
    by rw [mul_smul_comm, smul_mul_assoc], hQH _ hu, ?_, x, y, hx, hy, Q * a * ϖ, hQH _ ha, hconj⟩
  have hn1 : Quaternion.normSq Q * Quaternion.normSq ϖ = 1 := by rw [← map_mul, hQ1, map_one]
  rw [map_mul, map_mul, mul_comm (Quaternion.normSq Q), mul_assoc, hn1, mul_one, hnu]

end C1

/-! ## The group `C1` -/

section Closure

variable {ϖ : ℍ[ℚ_[2]]} {L : ℍ[ℚ_[2]] → Prop}

theorem P1_mul (hmul : ∀ y z, L y → L z → L (y * z)) (hinv : ∀ y z, L y → y * z = 1 → L z)
    (hconj : ∀ z, L z → L (qinv ϖ * z * ϖ)) (hsq : L (ϖ * ϖ)) (hQ1 : qinv ϖ * ϖ = 1)
    (hQ2 : ϖ * qinv ϖ = 1) {y z : ℍ[ℚ_[2]]} (hy : L y ∨ L (y * ϖ)) (hz : L z ∨ L (z * ϖ)) :
    L (y * z) ∨ L (y * z * ϖ) := by
  rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact Or.inl (hmul _ _ hy hz)
  · right; rw [mul_assoc]; exact hmul _ _ hy hz
  · right
    have e : y * z * ϖ = (y * ϖ) * (qinv ϖ * z * ϖ) := by
      rw [show (y * ϖ) * (qinv ϖ * z * ϖ) = y * (ϖ * qinv ϖ) * z * ϖ by noncomm_ring, hQ2, mul_one]
    rw [e]; exact hmul _ _ hy (hconj _ hz)
  · left
    have hW : L (qinv ϖ * qinv ϖ) := hinv _ _ hsq (by
      rw [show ϖ * ϖ * (qinv ϖ * qinv ϖ) = ϖ * (ϖ * qinv ϖ) * qinv ϖ by noncomm_ring, hQ2, mul_one, hQ2])
    have e : y * z = (y * ϖ) * (qinv ϖ * (z * ϖ) * ϖ) * (qinv ϖ * qinv ϖ) := by
      rw [show (y * ϖ) * (qinv ϖ * (z * ϖ) * ϖ) * (qinv ϖ * qinv ϖ) =
        y * (ϖ * qinv ϖ) * z * (ϖ * (ϖ * qinv ϖ) * qinv ϖ) by noncomm_ring, hQ2, mul_one, mul_one, hQ2,
        mul_one]
    rw [e]; exact hmul _ _ (hmul _ _ hy (hconj _ hz)) hW

theorem P1_inv (hinv : ∀ y z, L y → y * z = 1 → L z) (hmul : ∀ y z, L y → L z → L (y * z))
    (hconj : ∀ z, L z → L (qinv ϖ * z * ϖ)) (hsq : L (ϖ * ϖ))
    (hQ2 : ϖ * qinv ϖ = 1) {y z : ℍ[ℚ_[2]]} (hy : L y ∨ L (y * ϖ)) (h : y * z = 1) :
    L z ∨ L (z * ϖ) := by
  rcases hy with hy | hy
  · exact Or.inl (hinv _ _ hy h)
  · right
    have hw : L (qinv ϖ * z) := hinv _ _ hy (by
      rw [show y * ϖ * (qinv ϖ * z) = y * (ϖ * qinv ϖ) * z by noncomm_ring, hQ2, mul_one, h])
    have e : z * ϖ = (ϖ * ϖ) * (qinv ϖ * (qinv ϖ * z) * ϖ) := by
      rw [show (ϖ * ϖ) * (qinv ϖ * (qinv ϖ * z) * ϖ) = ϖ * (ϖ * qinv ϖ) * qinv ϖ * z * ϖ by noncomm_ring,
        hQ2, mul_one, hQ2, one_mul]
    rw [e]; exact hmul _ _ hsq (hconj _ hw)

end Closure

/-! ## The centralizer for `n ≡ 1 (mod 8)` -/

theorem toZMod_natCast_odd {k : ℕ} : PadicInt.toZMod ((8 * k + 1 : ℕ) : ℤ_[2]) = 1 := by
  rw [map_natCast]; push_cast
  rw [show (8 : ZMod 2) = 0 from rfl]; ring

theorem unit_of_toZMod {x : ℤ_[2]} (h : PadicInt.toZMod x ≠ 0) : ‖(x : ℚ_[2])‖ = 1 := by
  rw [← PadicInt.norm_def, ← PadicInt.isUnit_iff]
  by_contra hu
  have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[2] := hu
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hm
  exact h hm

theorem exists_two_mul_of_toZMod {x : ℤ_[2]} (h : PadicInt.toZMod x = 0) : ∃ y : ℤ_[2], x = 2 * y := by
  have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]; exact h
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hm
  obtain ⟨y, hy⟩ := hm
  exact ⟨y, by rw [← hy, mul_comm]; norm_num⟩

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

/-- **The core case analysis**: for `x, z ∈ ℤ_2` not both even, `x + zω ∈ R_2^×` or
`(x + zω)ϖ ∈ 2 R_2^×`. -/
theorem core1 {ω' : ℍ[ℚ_[2]]} (hω : IsHur (Zp 2) ω') {k : ℕ}
    (hω2 : ω' * ω' = -(((8 * k + 1 : ℕ) : ℚ_[2])) • 1)
    (hnrd : ∀ x z : ℚ_[2], Quaternion.normSq (x • (1 : ℍ[ℚ_[2]]) + z • ω') = x ^ 2 + ((8 * k + 1 : ℕ) : ℚ_[2]) * z ^ 2)
    (x z : ℤ_[2]) (hxz : PadicInt.toZMod x ≠ 0 ∨ PadicInt.toZMod z ≠ 0) :
    Loc2OK ω' ((x : ℚ_[2]) • 1 + (z : ℚ_[2]) • ω') ∨
      Loc2OK ω' (((x : ℚ_[2]) • 1 + (z : ℚ_[2]) • ω') * (1 + ω')) := by
  set n' : ℤ_[2] := ((8 * k + 1 : ℕ) : ℤ_[2]) with hn'
  have hn1 : PadicInt.toZMod n' = 1 := toZMod_natCast_odd
  have hnq : ((8 * k + 1 : ℕ) : ℚ_[2]) = (n' : ℚ_[2]) := by rw [hn']; push_cast; rfl
  have hHur : ∀ x z : ℤ_[2], IsHur (Zp 2) ((x : ℚ_[2]) • (1 : ℍ[ℚ_[2]]) + (z : ℚ_[2]) • ω') :=
    fun x z => (isHur_one.smul (mem_Zp.mpr x.2)).add (hω.smul (mem_Zp.mpr z.2))
  have hInR : ∀ x z : ℤ_[2], InR ω' ((x : ℚ_[2]) • (1 : ℍ[ℚ_[2]]) + (z : ℚ_[2]) • ω') :=
    fun x z => ⟨x, z, x.2, z.2, 0, isHur_zero, by simp⟩
  have hnorm : ∀ x z : ℤ_[2], PadicInt.toZMod (x ^ 2 + n' * z ^ 2) ≠ 0 →
      ‖Quaternion.normSq ((x : ℚ_[2]) • (1 : ℍ[ℚ_[2]]) + (z : ℚ_[2]) • ω')‖ = 1 := by
    intro x z h
    rw [hnrd, hnq]
    have := unit_of_toZMod h
    push_cast at this; exact this
  rcases zmod2_cases (PadicInt.toZMod x) with hx | hx <;>
    rcases zmod2_cases (PadicInt.toZMod z) with hz | hz
  · exfalso; rcases hxz with h | h
    · exact h hx
    · exact h hz
  · left
    refine ⟨1, one_ne_zero, _, by rw [one_smul], hHur x z, hnorm x z ?_, hInR x z⟩
    simp [hx, hz, hn1]
  · left
    refine ⟨1, one_ne_zero, _, by rw [one_smul], hHur x z, hnorm x z ?_, hInR x z⟩
    simp [hx, hz, hn1]
  · right
    obtain ⟨X', hX'⟩ := exists_two_mul_of_toZMod (x := x - n' * z) (by simp [hx, hz, hn1])
    obtain ⟨Z', hZ'⟩ := exists_two_mul_of_toZMod (x := x + z) (by
      simp [hx, hz]; rw [show (1 : ZMod 2) + 1 = 0 from rfl])
    have hsum : X' + Z' = x - 4 * (k : ℤ_[2]) * z := by
      have h2 : (2 : ℤ_[2]) * (X' + Z') = 2 * (x - 4 * (k : ℤ_[2]) * z) := by
        rw [mul_add, ← hX', ← hZ', hn']; push_cast; ring
      exact mul_left_cancel₀ (by norm_num) h2
    have htX : PadicInt.toZMod (X' + Z') = 1 := by
      have h4 : PadicInt.toZMod (4 : ℤ_[2]) = 0 := by rw [map_ofNat]; rfl
      rw [hsum, map_sub, map_mul, map_mul, hx, h4]; ring
    have hprod : ((x : ℚ_[2]) • (1 : ℍ[ℚ_[2]]) + (z : ℚ_[2]) • ω') * (1 + ω') =
        (2 : ℚ_[2]) • ((X' : ℚ_[2]) • (1 : ℍ[ℚ_[2]]) + (Z' : ℚ_[2]) • ω') := by
      have h2 : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := rfl
      have eX : (X' : ℚ_[2]) = ((x : ℚ_[2]) - (n' : ℚ_[2]) * z) / 2 := by
        have := congrArg (fun w : ℤ_[2] => (w : ℚ_[2])) hX'; simp only [PadicInt.coe_sub, PadicInt.coe_mul, h2] at this; rw [eq_div_iff two_ne_zero]; linear_combination -this
      have eZ : (Z' : ℚ_[2]) = ((x : ℚ_[2]) + z) / 2 := by
        have := congrArg (fun w : ℤ_[2] => (w : ℚ_[2])) hZ'; simp only [PadicInt.coe_add, PadicInt.coe_mul, h2] at this; rw [eq_div_iff two_ne_zero]; linear_combination -this
      rw [eX, eZ]
      simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, hω2, hnq]
      ext <;> simp <;> ring
    refine ⟨2, by norm_num, _, hprod, hHur X' Z', hnorm X' Z' ?_, hInR X' Z'⟩
    rw [map_add, map_pow, map_mul, map_pow, hn1, one_mul]
    rcases zmod2_cases (PadicInt.toZMod X') with h1 | h1 <;>
      rcases zmod2_cases (PadicInt.toZMod Z') with h2 | h2 <;>
      simp [h1, h2] at htX ⊢

end ZInQ.Contrib.HfxProof
