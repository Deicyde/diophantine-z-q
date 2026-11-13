import ZInQKernel.Contrib.GZTheta.New32

/-!
# gz-theta: the Fricke involution on the twists `f_d = f₁ ⊗ (·/d)`

For squarefree `d ≡ 1 (mod 4)` and `N = 32 d²`:

  `f_d(−1/(N τ)) = −χ_d(−32) · 32 d² · τ² · f_d(τ)`        (`cmForm_fricke`)

from Tau Ceti's formula `f_d(τ) = d⁻¹ ∑_a 𝓕χ_d(a) f₁(τ + a/d)`, the identity
`𝓕χ_d(a) = χ_d(a) 𝓕χ_d(1)` (`dft_jacobiChar`; it vanishes at non-units because `d` is
squarefree), and, for `a` prime to `d` and `b ≡ −(32a)⁻¹ (mod d)`,
`a/d − 1/(N τ) = W₃₂(X (τ + b/d))` with `X = (d, −b; −32a, (32ab+1)/d) ∈ Γ₀(32)`.
-/

open Complex Filter ModularForm CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Real Topology MatrixGroups

noncomputable section

namespace ZInQ.GZTheta

open ZInQ.Contrib.HeckeFE ZInQ.GZDecomp

/-! ### The Fourier transform of the Jacobi character -/

theorem jacobiChar_inv_unit (d : ℕ) [NeZero d] (u : (ZMod d)ˣ) :
    jacobiChar d ((u⁻¹ : (ZMod d)ˣ) : ZMod d) = jacobiChar d (u : ZMod d) := by
  have h1 : jacobiChar d (u : ZMod d) * jacobiChar d ((u⁻¹ : (ZMod d)ˣ) : ZMod d) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 := jacobiChar_sq_unit d u
  calc jacobiChar d ((u⁻¹ : (ZMod d)ˣ) : ZMod d)
      = jacobiChar d (u : ZMod d) ^ 2 * jacobiChar d ((u⁻¹ : (ZMod d)ˣ) : ZMod d) := by
        rw [h2, one_mul]
    _ = jacobiChar d (u : ZMod d) := by rw [sq, mul_assoc, h1, mul_one]

/-- For a non-unit `k` modulo squarefree odd `d` there is a unit `u` with `u k = k` and
`(u/d) = −1`. -/
theorem exists_unit_fix (d : ℕ) [NeZero d] (hsq : Squarefree d) (hodd : Odd d) (k : ZMod d)
    (hk : ¬ IsUnit k) : ∃ u : (ZMod d)ˣ, (u : ZMod d) * k = k ∧ jacobiChar d (u : ZMod d) = -1 := by
  have hnc : ¬ Nat.Coprime k.val d := by
    intro hc
    apply hk
    have := (ZMod.isUnit_iff_coprime k.val d).mpr hc
    rwa [ZMod.natCast_zmod_val] at this
  obtain ⟨p, hp, hpk, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  obtain ⟨d', rfl⟩ := hpd
  have hcop : Nat.Coprime p d' := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have := hsq p (Nat.mul_dvd_mul_left p h)
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hodd
    omega
  have hd'0 : d' ≠ 0 := by rintro rfl; simp at *
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  have hn0 : n ≠ 0 := by rintro rfl; exact hn ⟨0, by simp⟩
  let x := Nat.chineseRemainder hcop n.val 1
  have hx1 : (x : ℕ) ≡ n.val [MOD p] := x.2.1
  have hx2 : (x : ℕ) ≡ 1 [MOD d'] := x.2.2
  have hxp : ((x : ℕ) : ZMod p) = n := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hx1, ZMod.natCast_zmod_val]
  have hcx : Nat.Coprime (x : ℕ) (p * d') := by
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      apply hn0
      rw [← hxp, (ZMod.natCast_eq_zero_iff _ _).mpr h]
    · have := Nat.ModEq.gcd_eq hx2
      rw [Nat.gcd_one_left] at this
      exact this
  refine ⟨ZMod.unitOfCoprime (x : ℕ) hcx, ?_, ?_⟩
  · rw [ZMod.coe_unitOfCoprime]
    conv_rhs => rw [← ZMod.natCast_zmod_val k]
    conv_lhs => rw [← ZMod.natCast_zmod_val k, ← Nat.cast_mul]
    rw [ZMod.natCast_eq_natCast_iff]
    -- `(x − 1) k ≡ 0 (mod p d')`
    obtain ⟨k₁, hk₁⟩ := hpk
    have hx0 : 1 ≤ (x : ℕ) := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, Nat.coprime_zero_left] at hcx
      exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hcx)
    have h1 : d' ∣ (x : ℕ) - 1 := (Nat.modEq_iff_dvd' hx0).mp hx2.symm
    obtain ⟨t, ht⟩ := h1
    have : (x : ℕ) * k.val = k.val + p * d' * (t * k₁) := by
      have e : (x : ℕ) = 1 + d' * t := by omega
      rw [e, hk₁]; ring
    rw [this]
    exact (Nat.modEq_iff_dvd' (by omega)).mpr ⟨t * k₁, by omega⟩ |>.symm
  · rw [ZMod.coe_unitOfCoprime, jacobiChar_natCast]
    rw [jacobiSym.mul_right' _ hp.ne_zero hd'0]
    have hJp : jacobiSym ((x : ℕ) : ℤ) p = -1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym]
      exact (legendreSym.eq_neg_one_iff' p).mpr (by rw [hxp]; exact hn)
    have hJd : jacobiSym ((x : ℕ) : ℤ) d' = 1 := by
      rw [jacobiSym.mod_left]
      have : ((x : ℕ) : ℤ) % d' = 1 % d' := by
        have h := congrArg (fun m : ℕ => (m : ℤ)) hx2
        simpa [Int.natCast_mod] using h
      rw [this, ← jacobiSym.mod_left, jacobiSym.one_left]
    rw [hJp, hJd]
    norm_num

end ZInQ.GZTheta
