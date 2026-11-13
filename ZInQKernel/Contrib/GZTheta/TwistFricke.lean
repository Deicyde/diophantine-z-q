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


/-- **`𝓕χ_d(k) = χ_d(k) 𝓕χ_d(1)`** for squarefree odd `d`. -/
theorem dft_jacobiChar (d : ℕ) [NeZero d] (hsq : Squarefree d) (hodd : Odd d) (k : ZMod d) :
    ZMod.dft (⇑(jacobiChar d)) k = jacobiChar d k * ZMod.dft (⇑(jacobiChar d)) 1 := by
  by_cases hk : IsUnit k
  · obtain ⟨u, rfl⟩ := hk
    have h := ZMod.dft_comp_unitMul (⇑(jacobiChar d)) u⁻¹ 1
    have hfun : (fun j => jacobiChar d (((u⁻¹ : (ZMod d)ˣ) : ZMod d) * j)) =
        jacobiChar d ((u⁻¹ : (ZMod d)ˣ) : ZMod d) • ⇑(jacobiChar d) := by
      ext j; simp [map_mul]
    rw [hfun, map_smul, inv_inv, mul_one, Pi.smul_apply, smul_eq_mul, jacobiChar_inv_unit] at h
    exact h.symm
  · rw [MulChar.map_nonunit _ hk, zero_mul]
    obtain ⟨u, hu, hχu⟩ := exists_unit_fix d hsq hodd k hk
    have h := ZMod.dft_comp_unitMul (⇑(jacobiChar d)) u k
    have hfun : (fun j => jacobiChar d ((u : ZMod d) * j)) = (-1 : ℂ) • ⇑(jacobiChar d) := by
      ext j; simp [map_mul, hχu]
    have hk' : ((u⁻¹ : (ZMod d)ˣ) : ZMod d) * k = k := by
      conv_lhs => rw [← hu]
      rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [hfun, map_smul, hk', Pi.smul_apply, smul_eq_mul] at h
    have : (2 : ℂ) * ZMod.dft (⇑(jacobiChar d)) k = 0 := by linear_combination -h
    simpa using this


/-! ### The level-32 form at `a/d − 1/(32 d² τ)` -/

theorem etaQuot32_smul_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 32) (τ : ℍ) :
    etaQuot32 (γ • τ) = ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 2 * etaQuot32 τ := by
  have h := congrFun (etaQuot32_slash_eq hγ) τ
  rw [SL_slash_apply] at h
  have hD : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := mobius_denom_ne_zero (det_SL γ) τ.im_pos
  have hden : denom γ τ = (γ 1 0 : ℂ) * τ + γ 1 1 := by simp [ModularGroup.denom_apply]
  rw [hden, zpow_neg, zpow_two] at h
  field_simp at h
  linear_combination h

/-- For integers `a, b` with `d ∣ 32ab + 1`:
`f₁(a/d − 1/(32 d² τ)) = −32 d² τ² f₁(τ + b/d)`. -/
theorem F₁_shift_fricke {d : ℕ} (hd : 0 < d) {a b : ℤ} (hab : (d : ℤ) ∣ 32 * a * b + 1)
    (τ : ℍ) :
    F₁ ((a : ℂ) / d - 1 / (32 * (d : ℂ) ^ 2 * τ)) =
      -32 * (d : ℂ) ^ 2 * (τ : ℂ) ^ 2 * F₁ ((τ : ℂ) + (b : ℂ) / d) := by
  obtain ⟨δ, hδ⟩ := hab
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  -- `X = (d, −b; −32a, δ)`
  have hdet : (d : ℤ) * δ - (-b) * (-32 * a) = 1 := by linear_combination -hδ
  let X : SL(2, ℤ) := ⟨!![(d : ℤ), -b; -32 * a, δ], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  have hX : X ∈ Gamma0 32 := by
    rw [Gamma0_mem]
    show (((-32 * a : ℤ)) : ZMod 32) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨-a, by push_cast; ring⟩
  set τ' : ℍ := ⟨(τ : ℂ) + (b : ℂ) / d, by
    simp only [add_im, div_natCast_im, intCast_im, zero_div, add_zero]; exact τ.im_pos⟩ with hτ'
  have hw := etaQuot32_smul_of_mem hX τ'
  have hcoeX : ((X • τ' : ℍ) : ℂ) = ((d : ℂ) * τ' + (-b : ℤ)) / ((-32 * a : ℤ) * τ' + δ) := by
    rw [coe_smul_SL]; simp [X]
  have hdenX : ((-32 * a : ℤ) : ℂ) * τ' + δ ≠ 0 := mobius_denom_ne_zero hdet τ'.im_pos
  have hnum : (d : ℂ) * τ' + ((-b : ℤ) : ℂ) = (d : ℂ) * τ := by
    simp only [hτ', UpperHalfPlane.coe_mk]; push_cast; field_simp; ring
  -- the point
  have hpt : (a : ℂ) / d - 1 / (32 * (d : ℂ) ^ 2 * τ) = -1 / (32 * ((X • τ' : ℍ) : ℂ)) := by
    rw [hcoeX, hnum]
    have hδC : (d : ℂ) * δ = 32 * a * b + 1 := by exact_mod_cast hδ.symm
    simp only [hτ', UpperHalfPlane.coe_mk]
    push_cast
    field_simp
    linear_combination hδC
  rw [hpt, F₁_fricke (X • τ').im_pos]
  have e1 : F₁ ((X • τ' : ℍ) : ℂ) = etaQuot32 (X • τ') := rfl
  have e2 : F₁ ((τ : ℂ) + (b : ℂ) / d) = etaQuot32 τ' := rfl
  rw [e1, e2, hw]
  have hX10 : ((X 1 0 : ℤ) : ℂ) = ((-32 * a : ℤ) : ℂ) := by simp [X]
  have hX11 : ((X 1 1 : ℤ) : ℂ) = (δ : ℂ) := by simp [X]
  rw [hX10, hX11]
  have hprod : ((X • τ' : ℍ) : ℂ) * (((-32 * a : ℤ) : ℂ) * τ' + δ) = (d : ℂ) * τ := by
    rw [hcoeX, div_mul_cancel₀ _ hdenX, hnum]
  have : ((X • τ' : ℍ) : ℂ) ^ 2 * (((-32 * a : ℤ) : ℂ) * τ' + δ) ^ 2 = ((d : ℂ) * τ) ^ 2 := by
    rw [← hprod]; ring
  linear_combination (-32 : ℂ) * etaQuot32 τ' * this

end ZInQ.GZTheta
