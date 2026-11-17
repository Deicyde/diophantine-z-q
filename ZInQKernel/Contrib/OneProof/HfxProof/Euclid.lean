import ZInQKernel.Contrib.OneProof.T21Proof.GlobalStep
import ZInQKernel.Contrib.OneProof.TYZSquareOddness.Coordinates

/-!
# hfx-proof: the Hurwitz order is right Euclidean

Task hfx-proof. `O_B` (Hurwitz quaternions, `IsHurZ`) is right Euclidean for the reduced norm
(the approximation `exists_hurwitz_coordinates_norm_lt_one` of fork PR #39). Consequence used for
`B̂^× = B^× Ô_B^×` (`euclid_prime`): if `p` is prime, `β ∈ O_B`, `p ∣ nrd β` and `β ∉ p O_B`, the right
ideal `β O_B + p O_B` is `γ O_B` with `nrd γ = p`.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.T21Proof
open scoped Quaternion

/-- `ℤ ⊂ ℚ`. -/
abbrev ZS : Subring ℚ := (Int.castRingHom ℚ).range

/-- `y ∈ O_B` (integral Hurwitz coordinates). -/
abbrev IsHurZ (y : ℍ[ℚ]) : Prop := IsHur ZS y

theorem mem_ZS {x : ℚ} : x ∈ ZS ↔ ∃ m : ℤ, (m : ℚ) = x := by
  simp [ZS, RingHom.mem_range]

theorem isHurZ_natCast (m : ℕ) : IsHurZ (m : ℍ[ℚ]) := by
  have : ((m : ℚ) : ℍ[ℚ]) = (m : ℍ[ℚ]) := by norm_cast
  rw [← this]; exact isHur_coe (mem_ZS.mpr ⟨m, by norm_cast⟩)

/-- The reduced norm of an integral element is an integer. -/
theorem IsHurZ.normSq_int {y : ℍ[ℚ]} (hy : IsHurZ y) : ∃ k : ℤ, Quaternion.normSq y = k := by
  obtain ⟨k, hk⟩ := mem_ZS.mp hy.normSq_mem
  exact ⟨k, hk.symm⟩

/-- **Hurwitz approximation** (fork PR #39). -/
theorem exists_isHurZ_normSq_lt_one (q : ℍ[ℚ]) : ∃ δ : ℍ[ℚ], IsHurZ δ ∧ Quaternion.normSq (q - δ) < 1 := by
  obtain ⟨a, b, c, d, e, h⟩ := TYZSquareOddness.exists_hurwitz_coordinates_norm_lt_one q
  refine ⟨_, ?_, h⟩
  refine ⟨mem_ZS.mpr ⟨a + d, ?_⟩, mem_ZS.mpr ⟨b - d, ?_⟩, mem_ZS.mpr ⟨c - d, ?_⟩,
    mem_ZS.mpr ⟨2 * d + e, ?_⟩⟩ <;> simp [hc] <;> ring

/-- The right ideal `β O_B + p O_B`. -/
def InI (β : ℍ[ℚ]) (p : ℕ) (ξ : ℍ[ℚ]) : Prop :=
  ∃ a b : ℍ[ℚ], IsHurZ a ∧ IsHurZ b ∧ ξ = β * a + (p : ℍ[ℚ]) * b

theorem InI.mul_right {β : ℍ[ℚ]} {p : ℕ} {ξ δ : ℍ[ℚ]} (h : InI β p ξ) (hδ : IsHurZ δ) :
    InI β p (ξ * δ) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  exact ⟨a * δ, b * δ, ha.mul hδ, hb.mul hδ, by noncomm_ring⟩

theorem InI.sub {β : ℍ[ℚ]} {p : ℕ} {ξ ξ' : ℍ[ℚ]} (h : InI β p ξ) (h' : InI β p ξ') :
    InI β p (ξ - ξ') := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  obtain ⟨a', b', ha', hb', rfl⟩ := h'
  exact ⟨a - a', b - b', ha.sub ha', hb.sub hb', by noncomm_ring⟩

theorem InI.isHurZ {β : ℍ[ℚ]} {p : ℕ} (hβ : IsHurZ β) {ξ : ℍ[ℚ]} (h : InI β p ξ) : IsHurZ ξ := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  exact (hβ.mul ha).add ((isHurZ_natCast p).mul hb)

theorem normSq_nonneg' (y : ℍ[ℚ]) : 0 ≤ Quaternion.normSq y := Quaternion.normSq_nonneg

theorem normSq_pos' {y : ℍ[ℚ]} (hy : y ≠ 0) : 0 < Quaternion.normSq y :=
  lt_of_le_of_ne Quaternion.normSq_nonneg (Ne.symm (Quaternion.normSq_ne_zero.mpr hy))

theorem natCast_mul_eq_smul (p : ℕ) (b : ℍ[ℚ]) : (p : ℍ[ℚ]) * b = (p : ℚ) • b := by
  rw [← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]

/-- An element of the ideal of minimal positive norm generates it. -/
theorem InI.exists_gen {β : ℍ[ℚ]} (hβ : IsHurZ β) {p : ℕ} (hp : 0 < p) :
    ∃ γ, InI β p γ ∧ γ ≠ 0 ∧ ∀ ξ, InI β p ξ → ∃ δ, IsHurZ δ ∧ ξ = γ * δ := by
  classical
  have hex : ∃ k : ℕ, ∃ ξ, InI β p ξ ∧ ξ ≠ 0 ∧ Quaternion.normSq ξ = k := by
    refine ⟨p ^ 2, (p : ℍ[ℚ]), ⟨0, 1, isHur_zero, isHur_one, by simp⟩, ?_, ?_⟩
    · intro h
      have := congrArg Quaternion.normSq h
      rw [Quaternion.normSq_natCast, map_zero] at this
      have : (p : ℚ) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      exact hp.ne' (by exact_mod_cast this)
    · rw [Quaternion.normSq_natCast]; push_cast; ring
  obtain ⟨γ, hγI, hγ0, hγk⟩ := Nat.find_spec hex
  refine ⟨γ, hγI, hγ0, fun ξ hξ => ?_⟩
  obtain ⟨δ, hδ, hlt⟩ := exists_isHurZ_normSq_lt_one (γ⁻¹ * ξ)
  refine ⟨δ, hδ, ?_⟩
  set r := ξ - γ * δ with hr
  have hrI : InI β p r := hξ.sub (hγI.mul_right hδ)
  have hrq : r = γ * (γ⁻¹ * ξ - δ) := by
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hγ0, one_mul]
  have hnr : Quaternion.normSq r < Quaternion.normSq γ := by
    rw [hrq, map_mul]
    have hpos : 0 < Quaternion.normSq γ := normSq_pos' hγ0
    calc Quaternion.normSq γ * Quaternion.normSq (γ⁻¹ * ξ - δ) < Quaternion.normSq γ * 1 :=
          mul_lt_mul_of_pos_left hlt hpos
      _ = _ := mul_one _
  by_contra hne
  have hr0 : r ≠ 0 := fun h => hne (by rw [← sub_eq_zero]; exact h)
  obtain ⟨k, hk⟩ := (hrI.isHurZ hβ).normSq_int
  have hk0 : 0 ≤ k := by
    have := normSq_nonneg' r; rw [hk] at this; exact_mod_cast this
  have hmin := Nat.find_min' hex ⟨r, hrI, hr0, show Quaternion.normSq r = (k.toNat : ℕ) by
    rw [hk]; exact_mod_cast (Int.toNat_of_nonneg hk0).symm⟩
  rw [hγk, hk] at hnr
  have : (k : ℚ) < (Nat.find hex : ℚ) := hnr
  have : k < (Nat.find hex : ℤ) := by exact_mod_cast this
  omega

theorem isHurZ_inv_mul_of_eq {γ δ ξ : ℍ[ℚ]} (hγ : γ ≠ 0) (hδ : IsHurZ δ) (h : ξ = γ * δ) :
    IsHurZ (γ⁻¹ * ξ) := by
  rw [h, ← mul_assoc, inv_mul_cancel₀ hγ, one_mul]; exact hδ

/-- `nrd (1 + p c) ≡ 1 (mod p)` in Hurwitz coordinates. -/
theorem nrdH_one_add_smul (p : ℤ) (c : H4 ℤ) :
    nrdH (⟨1 + p * c.a0, p * c.a1, p * c.a2, p * c.a3⟩ : H4 ℤ) =
      1 + p * (2 * c.a0 - c.a3 + p * nrdH c) := by
  simp only [nrdH]; ring

/-- **`β O_B + p O_B` is principal of norm `p`** when `p ∣ nrd β` and `β ∉ p O_B`. -/
theorem euclid_prime {β : ℍ[ℚ]} (hβ : IsHurZ β) {p : ℕ} (hp : p.Prime)
    (hdvd : ∃ k : ℤ, Quaternion.normSq β = (p : ℚ) * k)
    (hnot : ¬ IsHurZ ((p : ℚ)⁻¹ • β)) :
    ∃ γ, IsHurZ γ ∧ Quaternion.normSq γ = p ∧ IsHurZ (γ⁻¹ * β) ∧ IsHurZ (γ⁻¹ * (p : ℍ[ℚ])) := by
  obtain ⟨γ, hγI, hγ0, hgen⟩ := InI.exists_gen hβ hp.pos
  have hγZ := hγI.isHurZ hβ
  obtain ⟨δ, hδ, hβδ⟩ := hgen β ⟨1, 0, isHur_one, isHur_zero, by simp⟩
  obtain ⟨δ', hδ', hpδ⟩ := hgen (p : ℍ[ℚ]) ⟨0, 1, isHur_zero, isHur_one, by simp⟩
  refine ⟨γ, hγZ, ?_, isHurZ_inv_mul_of_eq hγ0 hδ hβδ, isHurZ_inv_mul_of_eq hγ0 hδ' hpδ⟩
  obtain ⟨g, hg⟩ := hγZ.normSq_int
  obtain ⟨d, hd⟩ := hδ'.normSq_int
  have hp2 : g * d = (p : ℤ) ^ 2 := by
    have := congrArg Quaternion.normSq hpδ
    rw [map_mul, hg, hd, Quaternion.normSq_natCast] at this
    exact_mod_cast this.symm
  have hg0 : 0 < g := by
    have := normSq_pos' hγ0; rw [hg] at this; exact_mod_cast this
  have hd0 : 0 ≤ d := by
    have := normSq_nonneg' δ'; rw [hd] at this; exact_mod_cast this
  -- `g ∣ p²`, so `g ∈ {1, p, p²}`
  have hgdvd : g.natAbs ∣ p ^ 2 := by
    have : (g.natAbs : ℤ) ∣ ((p ^ 2 : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg hg0.le]; push_cast; exact ⟨d, hp2.symm⟩
    exact_mod_cast this
  rw [Nat.dvd_prime_pow hp] at hgdvd
  obtain ⟨i, hi, hgi⟩ := hgdvd
  have hgi' : g = (p : ℤ) ^ i := by
    rw [← Int.natAbs_of_nonneg hg0.le, hgi]; push_cast; rfl
  interval_cases i
  · -- `γ` is a unit: then `1 ∈ β O_B + p O_B`, impossible mod `p`
    exfalso
    rw [pow_zero] at hgi'
    obtain ⟨a, b, ha, hb, hab⟩ := hγI.mul_right hγZ.star
    have h1 : γ * star γ = 1 := by
      rw [Quaternion.self_mul_star, hg, hgi']; simp
    rw [h1] at hab
    -- norms: `nrd (1 - p b) = nrd β nrd a`
    have hab' : β * a = 1 - (p : ℍ[ℚ]) * b := by rw [eq_sub_iff_add_eq]; exact hab.symm
    have hn := congrArg Quaternion.normSq hab'
    obtain ⟨k, hk⟩ := hdvd
    obtain ⟨na, hna⟩ := ha.normSq_int
    -- integer coordinates of `b`
    obtain ⟨bz, hbz⟩ := isHur_iff.mp hb
    set c : H4 ℤ := ⟨(bz.a0 : ℚ).num, (bz.a1 : ℚ).num, (bz.a2 : ℚ).num, (bz.a3 : ℚ).num⟩
    have hint : ∀ x : ZS, ((x : ℚ).num : ℚ) = x := by
      intro x; obtain ⟨m, hm⟩ := mem_ZS.mp x.2; rw [← hm]; simp
    have hc1 : hc (1 - (p : ℍ[ℚ]) * b) = mapH (Int.castRingHom ℚ)
        ⟨1 + (-(p : ℤ)) * c.a0, (-(p : ℤ)) * c.a1, (-(p : ℤ)) * c.a2, (-(p : ℤ)) * c.a3⟩ := by
      rw [natCast_mul_eq_smul, hc_sub, hc_one, hc_smul, hbz]
      simp only [mapH, c, Subring.coe_subtype, eq_intCast]
      push_cast
      rw [hint, hint, hint, hint]
      ext <;> simp <;> ring
    rw [normSq_eq_nrdH (1 - _), hc1, ← map_nrdH, nrdH_one_add_smul, map_mul, hk, hna] at hn
    have hz : (k * na : ℤ) * p = 1 + -(p : ℤ) * (2 * c.a0 - c.a3 + -(p : ℤ) * nrdH c) := by
      have : ((k * na * p : ℤ) : ℚ) = ((1 + -(p : ℤ) * (2 * c.a0 - c.a3 + -(p : ℤ) * nrdH c) : ℤ) : ℚ) := by
        rw [eq_intCast] at hn; push_cast at hn ⊢; linarith
      exact_mod_cast this
    have : (p : ℤ) ∣ 1 := ⟨k * na + (2 * c.a0 - c.a3 + -(p : ℤ) * nrdH c), by linarith⟩
    have := Int.eq_one_of_dvd_one (by positivity) this
    have := hp.one_lt
    omega
  · rw [pow_one] at hgi'; rw [hg, hgi']; push_cast; rfl
  · -- `nrd γ = p²`: then `δ'` is a unit and `β ∈ p O_B`
    exfalso
    apply hnot
    have hd1 : d = 1 := by
      rw [hgi'] at hp2
      have hp0 : (0 : ℤ) < (p : ℤ) ^ 2 := by have := hp.pos; positivity
      nlinarith
    -- `γ = p δ'⁻¹`, so `p⁻¹ β = δ'⁻¹ δ = star δ' * δ`
    have hδ'0 : δ' ≠ 0 := by
      intro h; rw [h, map_zero] at hd; rw [hd1] at hd; norm_num at hd
    have hinv : δ'⁻¹ = star δ' := by
      rw [Quaternion.inv_def, hd, hd1]; simp
    have hγe : γ = (p : ℍ[ℚ]) * δ'⁻¹ := by
      rw [hpδ, mul_assoc, mul_inv_cancel₀ hδ'0, mul_one]
    have : (p : ℚ)⁻¹ • β = star δ' * δ := by
      rw [hβδ, hγe, ← hinv, mul_assoc]
      rw [natCast_mul_eq_smul, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast hp.ne_zero), one_smul]
    rw [this]
    exact hδ'.star.mul hδ

end ZInQ.Contrib.HfxProof
