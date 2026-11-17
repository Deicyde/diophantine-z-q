import ZInQKernel.Contrib.OneProof.AdelicX0.StrongApprox
import ZInQKernel.Contrib.TYZChain.Bridge

/-!
# h33-g5: TYZ's level `U`, the CM points `P_n = [h, 1]`, and `P_n ↦ τ_n`

Task h33-g5 (2026-11-17). Report: `docs/research/h33-g5.md`.

Tian–Yuan–Zhang (arXiv:1411.4728v1, §3.1):
* `U = {g ∈ U₀(32) : 4 ∣ a − d}` (Period7.tex L1183–1185), `f₀ : X_U → X₀(32)` the natural projection
  (L1187);
* the embeddings `K_n → M₂(ℚ)`, `√−n ↦ [[−1, 1/4], [−4(n+1), 1]]` for `n ≡ 5 (mod 8)` and
  `√−n ↦ [[δ, 2], [−(n+δ²)/2, −δ]]` for `n ≡ 7 (mod 8)`, `δ² ≡ −n (mod 128)` (L1225–1229);
* `P_n = [h, 1] ∈ X_U(ℂ)` with `h ∈ ℍ` the unique fixed point of `K_n^×` (L1236–1240).

This file defines these objects over the double coset space of `StrongApprox.lean` and proves
* `fixed_tyzEmb5_iff`, `fixed_tyzEmb7_iff`: the fixed points in `ℍ` of TYZ's matrices are exactly the
  kernel's `τ_n = (tyzForm n).tauH`, resp. `(tyzForm7 n).tauH` (with `δ = tyzDelta n`);
* `tyzP5_eq`, `tyzP7_eq`: `f₀(P_n) = [τ_n, 1]` in `GL₂(ℚ)⁺ \ (ℍ × GL₂(𝔸_f)/U₀(32))`, the point that the
  bijection `gamma0OrbitsEquiv` attaches to the `Γ₀(32)`-orbit of `τ_n`.

No `sorry`, no `axiom`.
-/

noncomputable section

open IsDedekindDomain Matrix UpperHalfPlane

namespace ZInQ.AdelicX0

open ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.CMBridge

/-! ## §1. TYZ's level `U ⊂ U₀(32)` -/

/-- **TYZ's `U = {g ∈ U₀(32) : 4 ∣ a − d}`** (Period7.tex L1183–1185). -/
def UTYZ : Subgroup (GL (Fin 2) Af) where
  carrier := {g | g ∈ U0 32 ∧ DvdZ 4 ((g : M2 Af) 0 0 - (g : M2 Af) 1 1)}
  mul_mem' := by
    rintro g h ⟨hg, c, hc, hgc⟩ ⟨hh, c', hc', hhc⟩
    refine ⟨mul_mem hg hh, ?_⟩
    obtain ⟨hgZ, -, e, he, hge⟩ := hg
    obtain ⟨hhZ, -, e', he', hhe⟩ := hh
    refine ⟨c * (h : M2 Af) 0 0 + (g : M2 Af) 1 1 * c' + 8 * (g : M2 Af) 0 1 * e' -
      8 * e * (h : M2 Af) 0 1, ?_, ?_⟩
    · refine sub_mem (add_mem (add_mem (mul_mem hc (hhZ 0 0)) (mul_mem (hgZ 1 1) hc'))
        (mul_mem (mul_mem (intCast_mem 8) (hgZ 0 1)) he')) (mul_mem (mul_mem (intCast_mem 8) he)
        (hhZ 0 1))
    · rw [Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      push_cast at hge hhe hgc hhc ⊢
      have h1 : (g : M2 Af) 0 0 = (g : M2 Af) 1 1 + 4 * c := by linear_combination hgc
      have h2 : (h : M2 Af) 0 0 = (h : M2 Af) 1 1 + 4 * c' := by linear_combination hhc
      rw [hge, hhe, h1]
      linear_combination (g : M2 Af) 1 1 * h2
  one_mem' := ⟨one_mem _, 0, Zhat.zero_mem, by simp⟩
  inv_mem' := by
    rintro g ⟨hg, c, hc, hgc⟩
    refine ⟨inv_mem hg, ?_⟩
    obtain ⟨-, hg', -⟩ := hg
    set h : M2 Af := ((g⁻¹ : GL (Fin 2) Af) : M2 Af)
    have e := Units.inv_mul g
    have e' := Units.mul_inv g
    have eq : ∀ i j, (h * (g : M2 Af)) i j = (1 : M2 Af) i j := fun i j => by rw [e]
    have eq' : ∀ i j, ((g : M2 Af) * h) i j = (1 : M2 Af) i j := fun i j => by
      show (((g : GL (Fin 2) Af) : M2 Af) * ((g⁻¹ : GL (Fin 2) Af) : M2 Af)) i j = _
      rw [e']
    have e00 := eq 0 0; have e01 := eq 0 1; have e10 := eq 1 0; have e11 := eq 1 1
    have f00 := eq' 0 0; have f11 := eq' 1 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11 f00 f11
    -- `h₀₀ − h₁₁ = −det(h)·(g₀₀ − g₁₁)`
    refine ⟨-(h 0 0 * h 1 1 - h 0 1 * h 1 0) * c,
      mul_mem (neg_mem (sub_mem (mul_mem (hg' 0 0) (hg' 1 1)) (mul_mem (hg' 0 1) (hg' 1 0)))) hc, ?_⟩
    show h 0 0 - h 1 1 = _
    have key : h 0 0 - h 1 1 = -(h 0 0 * h 1 1 - h 0 1 * h 1 0) *
        ((g : M2 Af) 0 0 - (g : M2 Af) 1 1) := by
      linear_combination h 1 1 * e00 - h 0 1 * e10 - h 0 0 * e11 + h 1 0 * e01
    rw [key, hgc]; push_cast; ring

theorem UTYZ_le : UTYZ ≤ U0 32 := fun _ hg => hg.1

/-! ## §2. Fixed points of `GL₂(ℚ)⁺` on `ℍ` -/

theorem toGLR_det_pos {M : GL (Fin 2) ℚ} (hM : 0 < (M : M2 ℚ).det) :
    0 < (Matrix.GeneralLinearGroup.det (toGLR M)).val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show 0 < ((M : M2 ℚ).map (algebraMap ℚ ℝ)).det
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simpa using hM

/-- **`M z = z` iff `c z² + (d − a) z − b = 0`**, for `M = [[a, b], [c, d]] ∈ GL₂(ℚ)⁺`. -/
theorem smul_eq_self_iff {M : GL (Fin 2) ℚ} (hM : 0 < (M : M2 ℚ).det) (z : ℍ) :
    toGLR M • z = z ↔
      ((M : M2 ℚ) 1 0 : ℂ) * (z : ℂ) ^ 2 + (((M : M2 ℚ) 1 1 : ℂ) - (M : M2 ℚ) 0 0) * z -
        ((M : M2 ℚ) 0 1 : ℂ) = 0 := by
  rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_smul_of_det_pos (toGLR_det_pos hM)]
  have hden := UpperHalfPlane.denom_ne_zero (toGLR M) z
  rw [div_eq_iff hden]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom] at hden ⊢
  have hc : ∀ i j, (((toGLR M : GL (Fin 2) ℝ) : M2 ℝ) i j : ℂ) = ((M : M2 ℚ) i j : ℂ) := by
    intro i j
    show ((algebraMap ℚ ℝ ((M : M2 ℚ) i j) : ℝ) : ℂ) = _
    simp
  simp only [hc]
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-! ## §3. The root of a Heegner form in `ℍ` -/

/-- `τ_Q` is a root of `A z² + B z + C`, and the only one in `ℍ`. -/
theorem heegner_root_iff {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) (z : ℍ) :
    (Q.A : ℂ) * (z : ℂ) ^ 2 + Q.B * z + Q.C = 0 ↔ z = Q.tauH := by
  set s : ℂ := (Real.sqrt (-(D : ℝ)) : ℂ)
  have hD : (0 : ℝ) ≤ -(D : ℝ) := by
    have := Q.D_neg; have : (D : ℝ) < 0 := by exact_mod_cast this
    linarith
  have hs2 : s ^ 2 = -(D : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hD]; push_cast; ring
  have hA : (Q.A : ℂ) ≠ 0 := by exact_mod_cast Q.A_pos.ne'
  have hdisc : (Q.B : ℂ) ^ 2 - 4 * Q.A * Q.C = D := by exact_mod_cast Q.disc
  set τ : ℂ := (-(Q.B : ℂ) + Complex.I * s) / (2 * Q.A)
  set τ' : ℂ := (-(Q.B : ℂ) - Complex.I * s) / (2 * Q.A)
  have hτ : (Q.tauH : ℂ) = τ := rfl
  have hnum : (-(Q.B : ℂ) + Complex.I * s) * (-(Q.B : ℂ) - Complex.I * s) = 4 * Q.A * Q.C := by
    linear_combination hdisc + hs2 - s ^ 2 * Complex.I_sq
  have hprod : (Q.A : ℂ) * (τ * τ') = Q.C := by
    simp only [τ, τ']; rw [div_mul_div_comm, hnum]; field_simp; ring
  have hsum : (Q.A : ℂ) * (τ + τ') = -Q.B := by
    simp only [τ, τ']; rw [← add_div]; field_simp; ring
  have hfac : ∀ w : ℂ, (Q.A : ℂ) * w ^ 2 + Q.B * w + Q.C = Q.A * (w - τ) * (w - τ') := by
    intro w
    have : (Q.A : ℂ) * (w - τ) * (w - τ') =
        Q.A * w ^ 2 - (Q.A * (τ + τ')) * w + Q.A * (τ * τ') := by ring
    rw [this, hsum, hprod]; ring
  constructor
  · intro h
    rw [hfac] at h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hA
      · exact UpperHalfPlane.ext (by rw [hτ]; exact sub_eq_zero.mp h)
    · exfalso
      have hz := sub_eq_zero.mp h
      have him : (z : ℂ).im = τ'.im := by rw [hz]
      have hτ'im : τ'.im = -(Real.sqrt (-(D : ℝ)) / (2 * Q.A)) := by
        have h2 : (2 * (Q.A : ℂ)) = ((2 * (Q.A : ℝ) : ℝ) : ℂ) := by push_cast; ring
        simp only [τ', h2, Complex.div_ofReal_im]
        simp [s]
        ring
      have hpos : 0 ≤ Real.sqrt (-(D : ℝ)) / (2 * Q.A) := by
        have : (0 : ℝ) < Q.A := by exact_mod_cast Q.A_pos
        positivity
      have := z.im_pos
      rw [UpperHalfPlane.coe_im] at him
      linarith
  · rintro rfl
    rw [hfac, hτ]; ring

/-! ## §4. TYZ's embeddings and their fixed points -/

/-- **TYZ's image of `√−n` for `n ≡ 5 (mod 8)`: `[[−1, 1/4], [−4(n+1), 1]]`** (L1225–1227). -/
def tyzMat5 (n : ℕ) : M2 ℚ := !![-1, 1 / 4; -4 * ((n : ℚ) + 1), 1]

theorem tyzMat5_det (n : ℕ) : (tyzMat5 n).det = n := by
  rw [tyzMat5, Matrix.det_fin_two_of]; ring

/-- The embedding as an element of `GL₂(ℚ)⁺` (for `n ≠ 0`). -/
def tyzEmb5 (n : ℕ) (hn : n ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (tyzMat5 n) (by rw [tyzMat5_det]; exact_mod_cast hn)

/-- **TYZ's image of `√−n` for `n ≡ 7 (mod 8)`: `[[δ, 2], [−(n+δ²)/2, −δ]]`** (L1225–1229), with
`δ = tyzDelta n` (an integer with `δ² ≡ −n (mod 128)`, `tyzDelta_spec`). -/
def tyzMat7 (n : ℕ) : M2 ℚ :=
  !![(tyzDelta n : ℚ), 2; -(((n : ℚ) + (tyzDelta n : ℚ) ^ 2) / 2), -(tyzDelta n : ℚ)]

theorem tyzMat7_det (n : ℕ) : (tyzMat7 n).det = n := by
  rw [tyzMat7, Matrix.det_fin_two_of]; ring

def tyzEmb7 (n : ℕ) (hn : n ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (tyzMat7 n) (by rw [tyzMat7_det]; exact_mod_cast hn)

theorem n_ne_zero_of_mod5 {n : ℕ} (hn : n % 8 = 5) : n ≠ 0 := by omega
theorem n_ne_zero_of_mod7 {n : ℕ} (hn : n % 8 = 7) : n ≠ 0 := by omega

/-- **The fixed points in `ℍ` of TYZ's matrix for `n ≡ 5` are exactly `τ_n = (tyzForm n).tauH`.** -/
theorem fixed_tyzEmb5_iff {n : ℕ} (hn : n % 8 = 5) (z : ℍ) :
    toGLR (tyzEmb5 n (n_ne_zero_of_mod5 hn)) • z = z ↔ z = (tyzForm n hn).tauH := by
  have hpos : 0 < ((tyzEmb5 n (n_ne_zero_of_mod5 hn) : GL (Fin 2) ℚ) : M2 ℚ).det := by
    show 0 < (tyzMat5 n).det
    rw [tyzMat5_det]; exact_mod_cast Nat.pos_of_ne_zero (n_ne_zero_of_mod5 hn)
  rw [smul_eq_self_iff hpos, ← heegner_root_iff]
  show ((tyzMat5 n) 1 0 : ℂ) * (z : ℂ) ^ 2 + (((tyzMat5 n) 1 1 : ℂ) - (tyzMat5 n) 0 0) * z -
      ((tyzMat5 n) 0 1 : ℂ) = 0 ↔ _
  simp only [tyzMat5, tyzForm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  constructor
  · intro h; linear_combination (-4 : ℂ) * h
  · intro h; linear_combination (-1 / 4 : ℂ) * h

/-- **The fixed points in `ℍ` of TYZ's matrix for `n ≡ 7` are exactly `(tyzForm7 n).tauH`.** -/
theorem fixed_tyzEmb7_iff {n : ℕ} (hn : n % 8 = 7) (z : ℍ) :
    toGLR (tyzEmb7 n (n_ne_zero_of_mod7 hn)) • z = z ↔ z = (tyzForm7 n hn).tauH := by
  have hpos : 0 < ((tyzEmb7 n (n_ne_zero_of_mod7 hn) : GL (Fin 2) ℚ) : M2 ℚ).det := by
    show 0 < (tyzMat7 n).det
    rw [tyzMat7_det]; exact_mod_cast Nat.pos_of_ne_zero (n_ne_zero_of_mod7 hn)
  rw [smul_eq_self_iff hpos, ← heegner_root_iff]
  show ((tyzMat7 n) 1 0 : ℂ) * (z : ℂ) ^ 2 + (((tyzMat7 n) 1 1 : ℂ) - (tyzMat7 n) 0 0) * z -
      ((tyzMat7 n) 0 1 : ℂ) = 0 ↔ _
  have h4 : ((((n : ℤ) + (tyzDelta n : ℤ) ^ 2) / 4 : ℤ) : ℂ) = ((n : ℂ) + (tyzDelta n : ℂ) ^ 2) / 4 := by
    have hd := tyzDelta_dvd hn
    obtain ⟨k, hk⟩ := hd
    have : ((n : ℤ) + (tyzDelta n : ℤ) ^ 2) = 4 * (32 * k) := by linarith
    rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
    have hc : ((n : ℂ) + (tyzDelta n : ℂ) ^ 2) = ((4 * (32 * k) : ℤ) : ℂ) := by
      rw [← this]; push_cast; ring
    rw [hc]; push_cast; ring
  simp only [tyzMat7, tyzForm7, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [h4]
  push_cast
  constructor
  · intro h; linear_combination (-1 / 2 : ℂ) * h
  · intro h; linear_combination (-2 : ℂ) * h

/-! ## §5. The CM points `P_n = [h, 1] ∈ X_U(ℂ)` -/

open Classical in
/-- `h ∈ ℍ`, the fixed point of `M` (junk `I` if there is none). -/
def fixedPt (M : GL (Fin 2) ℚ) : ℍ :=
  if h : ∃ z : ℍ, toGLR M • z = z then h.choose else UpperHalfPlane.I

theorem fixedPt_spec {M : GL (Fin 2) ℚ} (h : ∃ z : ℍ, toGLR M • z = z) :
    toGLR M • fixedPt M = fixedPt M := by
  unfold fixedPt
  split_ifs
  exact h.choose_spec

/-- **TYZ's CM point `P_n = [h, 1] ∈ X_U(ℂ)` for `n ≡ 5 (mod 8)`** (L1236–1240), `h` the fixed point of
the image of `√−n` (hence of `K_n^×`) in `ℍ`. -/
def tyzP5 (n : ℕ) (hn : n % 8 = 5) : Sh UTYZ :=
  toSh UTYZ (fixedPt (tyzEmb5 n (n_ne_zero_of_mod5 hn)))

/-- **TYZ's CM point `P_n = [h, 1]` for `n ≡ 7 (mod 8)`** (L1236–1240). -/
def tyzP7 (n : ℕ) (hn : n % 8 = 7) : Sh UTYZ :=
  toSh UTYZ (fixedPt (tyzEmb7 n (n_ne_zero_of_mod7 hn)))

theorem fixedPt_tyzEmb5 {n : ℕ} (hn : n % 8 = 5) :
    fixedPt (tyzEmb5 n (n_ne_zero_of_mod5 hn)) = (tyzForm n hn).tauH :=
  (fixed_tyzEmb5_iff hn _).mp
    (fixedPt_spec ⟨_, (fixed_tyzEmb5_iff hn (tyzForm n hn).tauH).mpr rfl⟩)

theorem fixedPt_tyzEmb7 {n : ℕ} (hn : n % 8 = 7) :
    fixedPt (tyzEmb7 n (n_ne_zero_of_mod7 hn)) = (tyzForm7 n hn).tauH :=
  (fixed_tyzEmb7_iff hn _).mp
    (fixedPt_spec ⟨_, (fixed_tyzEmb7_iff hn (tyzForm7 n hn).tauH).mpr rfl⟩)

/-- **`P_n = [τ_n, 1]` in `X_U(ℂ)`, `n ≡ 5`** (the leaf's `τ_n = (tyzForm n).tauH`). -/
theorem tyzP5_eq {n : ℕ} (hn : n % 8 = 5) : tyzP5 n hn = toSh UTYZ (tyzForm n hn).tauH := by
  rw [tyzP5, fixedPt_tyzEmb5]

theorem tyzP7_eq {n : ℕ} (hn : n % 8 = 7) : tyzP7 n hn = toSh UTYZ (tyzForm7 n hn).tauH := by
  rw [tyzP7, fixedPt_tyzEmb7]

/-- **`f₀(P_n) = [τ_n, 1] ∈ X₀(32)(ℂ)`, `n ≡ 5`**: under the bijection `Γ₀(32) \ ℍ ≃ X_{U₀(32)}(ℂ)°`
(`gamma0OrbitsEquiv`), `f₀(P_n)` is the orbit of `τ_n`. -/
theorem f0_tyzP5 {n : ℕ} (hn : n % 8 = 5) :
    shMap UTYZ_le (tyzP5 n hn) = toSh (U0 32) (tyzForm n hn).tauH := by
  rw [tyzP5_eq, shMap_toSh]

theorem f0_tyzP7 {n : ℕ} (hn : n % 8 = 7) :
    shMap UTYZ_le (tyzP7 n hn) = toSh (U0 32) (tyzForm7 n hn).tauH := by
  rw [tyzP7_eq, shMap_toSh]

theorem f0_tyzP5_orbit {n : ℕ} (hn : n % 8 = 5) :
    shMap UTYZ_le (tyzP5 n hn) = gamma0OrbitsEquiv 32 (by norm_num) (Quotient.mk _ (tyzForm n hn).tauH) :=
  f0_tyzP5 hn

theorem f0_tyzP7_orbit {n : ℕ} (hn : n % 8 = 7) :
    shMap UTYZ_le (tyzP7 n hn) =
      gamma0OrbitsEquiv 32 (by norm_num) (Quotient.mk _ (tyzForm7 n hn).tauH) :=
  f0_tyzP7 hn

end ZInQ.AdelicX0
