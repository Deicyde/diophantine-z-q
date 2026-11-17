import ZInQKernel.Contrib.GZTheta.NewCMFinal

/-!
# atkin-li: the Fricke involution on a quadratic twist, at any level

Task atkin-li. Generalizes gz-theta's `cmForm_fricke` (level 32) to a cusp form `G` of any level
`M` with trivial nebentypus and a Fricke identity `G(−1/(Mz)) = c z² G(z)`: for `r` odd squarefree
prime to `M` and `χ = (·/r)`,

  `(G ⊗ χ)(−1/(M r² τ)) = c r² χ(−M) τ² (G ⊗ χ)(τ)`              (`twist_fricke`)

from Tau Ceti's formula `(G ⊗ χ)(τ) = r⁻¹ ∑_a 𝓕χ(a) G(τ + a/r)`, gz-theta's
`𝓕χ(a) = χ(a) 𝓕χ(1)` (`dft_jacobiChar`), and, for `a` prime to `r` and `b ≡ −(Ma)⁻¹ (mod r)`,
`a/r − 1/(M r² τ) = W_M(X (τ + b/r))` with `X = (r, −b; −Ma, (Mab+1)/r) ∈ Γ₀(M)`.
-/

open Complex Filter ModularForm CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Real Topology MatrixGroups

noncomputable section

namespace ZInQ.GZTheta

open ZInQ.Contrib.HeckeFE ZInQ.GZDecomp

/-! ### Functions on `ℍ` as functions on `ℂ` -/

/-- A function on `ℍ`, extended by `0` to `ℂ`. -/
def extH (f : ℍ → ℂ) (z : ℂ) : ℂ := if h : 0 < z.im then f ⟨z, h⟩ else 0

theorem extH_mk (f : ℍ → ℂ) (z : ℂ) (h : 0 < z.im) : extH f z = f ⟨z, h⟩ := dif_pos h

theorem extH_coe (f : ℍ → ℂ) (τ : ℍ) : extH f (τ : ℂ) = f τ := by
  rw [extH_mk f _ τ.im_pos]

theorem im_neg_inv_mul_pos {M : ℝ} (hM : 0 < M) (w : ℍ) : 0 < (-1 / ((M : ℂ) * w)).im := by
  have hz : 0 < ((M : ℂ) * w).im := by
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]; exact mul_pos hM w.im_pos
  have hne : ((M : ℂ) * w) ≠ 0 := fun h => by rw [h] at hz; simp at hz
  rw [neg_div, one_div, neg_im, inv_im, neg_div, neg_neg]
  exact div_pos hz (Complex.normSq_pos.mpr hne)

/-! ### Forms of trivial nebentypus are `Γ₀(M)`-invariant -/

theorem charOne_smul {M : ℕ} [NeZero M] {G : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2}
    (hG : G ∈ cuspFormCharSpace 2 (1 : (ZMod M)ˣ →* ℂˣ)) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M)
    (τ : ℍ) : G (γ • τ) = ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 2 * G τ := by
  have h := congrFun ((TauCeti.mem_cuspFormCharSpace_one_iff G).mp hG _
    (Subgroup.mem_map_of_mem _ hγ)) τ
  have h' : (⇑G ∣[(2 : ℤ)] γ) τ = G τ := h
  rw [SL_slash_apply] at h'
  clear h
  have h := h'
  have hD : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := mobius_denom_ne_zero (det_SL γ) τ.im_pos
  have hden : denom γ τ = (γ 1 0 : ℂ) * τ + γ 1 1 := by simp [ModularGroup.denom_apply]
  rw [hden, zpow_neg, zpow_two] at h
  field_simp at h
  linear_combination h

/-! ### The Fricke identity at shifted points -/

/-- For integers `a, b` with `r ∣ Mab + 1`:
`G(a/r − 1/(M r² τ)) = c r² τ² G(τ + b/r)`. -/
theorem shift_fricke {M r : ℕ} [NeZero M] (hr : 0 < r) {G : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2}
    (hG : G ∈ cuspFormCharSpace 2 (1 : (ZMod M)ˣ →* ℂˣ)) {c : ℂ}
    (hfr : ∀ (z : ℂ) (hz : 0 < z.im) (hz' : 0 < (-1 / ((M : ℂ) * z)).im),
      G ⟨-1 / ((M : ℂ) * z), hz'⟩ = c * z ^ 2 * G ⟨z, hz⟩)
    {a b : ℤ} (hab : (r : ℤ) ∣ M * a * b + 1) (τ : ℍ) :
    extH G ((a : ℂ) / r - 1 / ((M : ℂ) * (r : ℂ) ^ 2 * τ)) =
      c * (r : ℂ) ^ 2 * (τ : ℂ) ^ 2 * extH G ((τ : ℂ) + (b : ℂ) / r) := by
  obtain ⟨δ, hδ⟩ := hab
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  -- `X = (r, −b; −Ma, δ)`
  have hdet : (r : ℤ) * δ - (-b) * (-(M : ℤ) * a) = 1 := by linear_combination -hδ
  let X : SL(2, ℤ) := ⟨!![(r : ℤ), -b; -(M : ℤ) * a, δ], by
    rw [Matrix.det_fin_two_of]; exact hdet⟩
  have hX : X ∈ Gamma0 M := by
    rw [Gamma0_mem]
    show (((-(M : ℤ) * a : ℤ)) : ZMod M) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨-a, by ring⟩
  set τ' : ℍ := ⟨(τ : ℂ) + (b : ℂ) / r, by
    simp only [add_im, div_natCast_im, intCast_im, zero_div, add_zero]; exact τ.im_pos⟩ with hτ'
  have hw := charOne_smul hG hX τ'
  have hcoeX : ((X • τ' : ℍ) : ℂ) = ((r : ℂ) * τ' + (-b : ℤ)) / ((-(M : ℤ) * a : ℤ) * τ' + δ) := by
    rw [coe_smul_SL]; simp [X]
  have hdenX : ((-(M : ℤ) * a : ℤ) : ℂ) * τ' + δ ≠ 0 := mobius_denom_ne_zero hdet τ'.im_pos
  have hnum : (r : ℂ) * τ' + ((-b : ℤ) : ℂ) = (r : ℂ) * τ := by
    simp only [hτ', UpperHalfPlane.coe_mk]; push_cast; field_simp; ring
  -- the point
  have hpt : (a : ℂ) / r - 1 / ((M : ℂ) * (r : ℂ) ^ 2 * τ) = -1 / ((M : ℂ) * ((X • τ' : ℍ) : ℂ)) := by
    rw [hcoeX, hnum]
    have hδC : (r : ℂ) * δ = M * a * b + 1 := by exact_mod_cast hδ.symm
    simp only [hτ', UpperHalfPlane.coe_mk]
    push_cast
    field_simp
    linear_combination hδC
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hpos := im_neg_inv_mul_pos hM0 (X • τ')
  push_cast at hpos
  rw [hpt, extH_mk _ _ hpos, hfr _ (X • τ').im_pos hpos]
  have e1 : G ⟨((X • τ' : ℍ) : ℂ), (X • τ').im_pos⟩ = G (X • τ') := rfl
  have e2 : extH G ((τ : ℂ) + (b : ℂ) / r) = G τ' := extH_mk _ _ τ'.im_pos
  rw [e1, e2, hw]
  have hX10 : ((X 1 0 : ℤ) : ℂ) = ((-(M : ℤ) * a : ℤ) : ℂ) := by simp [X]
  have hX11 : ((X 1 1 : ℤ) : ℂ) = (δ : ℂ) := by simp [X]
  rw [hX10, hX11]
  have hprod : ((X • τ' : ℍ) : ℂ) * (((-(M : ℤ) * a : ℤ) : ℂ) * τ' + δ) = (r : ℂ) * τ := by
    rw [hcoeX, div_mul_cancel₀ _ hdenX, hnum]
  have : ((X • τ' : ℍ) : ℂ) ^ 2 * (((-(M : ℤ) * a : ℤ) : ℂ) * τ' + δ) ^ 2 = ((r : ℂ) * τ) ^ 2 := by
    rw [← hprod]; ring
  linear_combination c * G τ' * this

/-! ### The involution `u ↦ −(Mu)⁻¹` -/

/-- `σ(u) = −(M u)⁻¹` on the units modulo `r`. -/
def sigM {M r : ℕ} [NeZero r] (hM : Nat.Coprime M r) (u : (ZMod r)ˣ) : (ZMod r)ˣ :=
  -(ZMod.unitOfCoprime M hM * u)⁻¹

theorem sigM_sigM {M r : ℕ} [NeZero r] (hM : Nat.Coprime M r) (u : (ZMod r)ˣ) :
    sigM hM (sigM hM u) = u := by
  unfold sigM
  rw [mul_neg, inv_neg, neg_neg, mul_inv_rev, inv_inv, mul_comm (ZMod.unitOfCoprime M hM) u,
    mul_inv_cancel_right]

theorem jacobiChar_sigM {M r : ℕ} [NeZero r] (hM : Nat.Coprime M r) (u : (ZMod r)ˣ) :
    jacobiChar r ((sigM hM u : (ZMod r)ˣ) : ZMod r) =
      jacobiChar r (-(M : ZMod r)) * jacobiChar r (u : ZMod r) := by
  unfold sigM
  rw [Units.val_neg, show -((((ZMod.unitOfCoprime M hM * u)⁻¹ : (ZMod r)ˣ)) : ZMod r) =
    (-1 : ZMod r) * (((ZMod.unitOfCoprime M hM * u)⁻¹ : (ZMod r)ˣ) : ZMod r) by ring,
    map_mul, jacobiChar_inv_unit, Units.val_mul, map_mul, ZMod.coe_unitOfCoprime]
  rw [show -(M : ZMod r) = (-1 : ZMod r) * (M : ZMod r) by ring, map_mul]
  ring

theorem sigM_spec {M r : ℕ} [NeZero r] (hM : Nat.Coprime M r) (u : (ZMod r)ˣ) :
    (r : ℤ) ∣ M * ((u : ZMod r).val : ℤ) * (((sigM hM u : (ZMod r)ˣ) : ZMod r).val : ℤ) + 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  unfold sigM
  rw [Units.val_neg, mul_neg]
  have : (M : ZMod r) * (u : ZMod r) =
      ((ZMod.unitOfCoprime M hM * u : (ZMod r)ˣ) : ZMod r) := by
    rw [Units.val_mul, ZMod.coe_unitOfCoprime]
  rw [this, Units.mul_inv]
  ring

theorem jacobiChar_negM_sq {M r : ℕ} [NeZero r] (hM : Nat.Coprime M r) :
    jacobiChar r (-(M : ZMod r)) ^ 2 = 1 := by
  have hu : IsUnit (-(M : ZMod r)) := ((ZMod.isUnit_iff_coprime M r).mpr hM).neg
  have := jacobiChar_sq_unit r hu.unit
  rwa [IsUnit.unit_spec] at this

/-! ### The Fricke identity for the twist -/

/-- **The Fricke involution on `G ⊗ (·/r)`**:
`(G ⊗ χ)(−1/(M r² τ)) = c r² χ(−M) τ² (G ⊗ χ)(τ)`. -/
theorem twist_fricke {M r : ℕ} [NeZero M] [NeZero r] (hsq : Squarefree r) (hodd : Odd r)
    (hcop : Nat.Coprime M r) {G : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2}
    (hG : G ∈ cuspFormCharSpace 2 (1 : (ZMod M)ˣ →* ℂˣ)) {c : ℂ}
    (hfr : ∀ (z : ℂ) (hz : 0 < z.im) (hz' : 0 < (-1 / ((M : ℂ) * z)).im),
      G ⟨-1 / ((M : ℂ) * z), hz'⟩ = c * z ^ 2 * G ⟨z, hz⟩) (τ : ℍ)
    (hτ' : 0 < (-1 / (((M * r ^ 2 : ℕ) : ℂ) * τ)).im) :
    CuspForm.twist (jacobiChar r) (dvd_twist_left M r) (dvd_twist_right M r) G
        ⟨-1 / (((M * r ^ 2 : ℕ) : ℂ) * τ), hτ'⟩ =
      c * (r : ℂ) ^ 2 * jacobiChar r (-(M : ZMod r)) * (τ : ℂ) ^ 2 *
        CuspForm.twist (jacobiChar r) (dvd_twist_left M r) (dvd_twist_right M r) G τ := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hval : ∀ (a : ZMod r) (w : ℍ), G (((a.val : ℝ) / r) +ᵥ w) =
      extH G (((a.val : ℕ) : ℂ) / r + w) := by
    intro a w
    rw [← extH_coe (⇑G)]
    congr 1
    simp only [UpperHalfPlane.coe_vadd]
    push_cast; ring
  rw [CuspForm.twist_apply, CuspForm.twist_apply]
  simp only [hval]
  set χ := jacobiChar r with hχ
  have hdft : ∀ k, ZMod.dft (⇑χ) k = χ k * ZMod.dft (⇑χ) 1 := dft_jacobiChar r hsq hodd
  generalize ZMod.dft (⇑χ) 1 = Gs at hdft
  simp only [hdft]
  have hlev : (((M * r ^ 2 : ℕ) : ℂ)) = (M : ℂ) * (r : ℂ) ^ 2 := by push_cast; ring
  -- the left sum, over the units
  have hL : ∑ a : ZMod r, χ a * Gs * extH G (((a.val : ℕ) : ℂ) / r +
        ((⟨-1 / (((M * r ^ 2 : ℕ) : ℂ) * τ), hτ'⟩ : ℍ) : ℂ)) =
      ∑ u : (ZMod r)ˣ, χ (u : ZMod r) * Gs * (c * (r : ℂ) ^ 2 * (τ : ℂ) ^ 2 *
        extH G ((τ : ℂ) + ((((sigM hcop u : (ZMod r)ˣ) : ZMod r).val : ℕ) : ℂ) / r)) := by
    rw [sum_zmod_eq_sum_units _ (fun a ha => by rw [MulChar.map_nonunit _ ha]; ring)]
    refine Finset.sum_congr rfl fun u _ => ?_
    have h := shift_fricke hr0 hG hfr (sigM_spec hcop u) τ
    push_cast at h
    simp only [UpperHalfPlane.coe_mk]
    rw [hlev, show (((u : ZMod r).val : ℕ) : ℂ) / r + -1 / ((M : ℂ) * (r : ℂ) ^ 2 * τ) =
      (((u : ZMod r).val : ℕ) : ℂ) / r - 1 / ((M : ℂ) * (r : ℂ) ^ 2 * τ) by ring, h]
  -- reindex by `σ`
  have hR : ∑ u : (ZMod r)ˣ, χ (u : ZMod r) * Gs * (c * (r : ℂ) ^ 2 * (τ : ℂ) ^ 2 *
        extH G ((τ : ℂ) + ((((sigM hcop u : (ZMod r)ˣ) : ZMod r).val : ℕ) : ℂ) / r)) =
      c * (r : ℂ) ^ 2 * χ (-(M : ZMod r)) * (τ : ℂ) ^ 2 *
        ∑ b : ZMod r, χ b * Gs * extH G (((b.val : ℕ) : ℂ) / r + τ) := by
    rw [sum_zmod_eq_sum_units (fun b => χ b * Gs * extH G (((b.val : ℕ) : ℂ) / r + τ))
      (fun a ha => by rw [MulChar.map_nonunit _ ha]; ring), Finset.mul_sum]
    let e : (ZMod r)ˣ ≃ (ZMod r)ˣ := ⟨sigM hcop, sigM hcop, sigM_sigM hcop, sigM_sigM hcop⟩
    refine Fintype.sum_equiv e _ _ fun u => ?_
    simp only [e, Equiv.coe_fn_mk]
    have hχσσ : χ (u : ZMod r) = χ (-(M : ZMod r)) *
        χ ((sigM hcop u : (ZMod r)ˣ) : ZMod r) := by
      have := jacobiChar_sigM hcop (sigM hcop u)
      rw [sigM_sigM] at this
      exact this
    rw [hχσσ]
    rw [add_comm (τ : ℂ)]
    ring
  rw [hL, hR]
  ring

end ZInQ.GZTheta
