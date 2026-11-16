import ZInQKernel.Contrib.TYZGenus.CM
import Mathlib.NumberTheory.Modular

/-!
# gz-hl3: Heegner representatives exist (glue `HeegnerRepsExist`, proved)

Development file; merged into `HL3.lean`.
-/

noncomputable section

open UpperHalfPlane ZInQ.Contrib.TYZGenus.CM
open scoped Modular MatrixGroups

namespace ZInQ.GZHL3

/-- (copy) residue. -/
def HasResidue {N : ℕ} {D : ℤ} (β : ℤ) (Q : HeegnerForm N D) : Prop := (2 * N : ℤ) ∣ Q.B - β

/-- (copy) `Γ₀(N)`-equivalence. -/
def Gamma0Equiv {N : ℕ} {D : ℤ} (Q Q' : HeegnerForm N D) : Prop :=
  ∃ γ ∈ CongruenceSubgroup.Gamma0 N, γ • Q.tauH = Q'.tauH

/-- (copy) representatives. -/
def IsHeegnerReps (N : ℕ) (D β : ℤ) (S : Finset (HeegnerForm N D)) : Prop :=
  (∀ Q ∈ S, HasResidue β Q) ∧
    ∀ Q : HeegnerForm N D, HasResidue β Q → ∃! Q', Q' ∈ S ∧ Gamma0Equiv Q Q'

namespace Reps

/-! ### CM points -/

theorem sqrt_sq_D {D : ℤ} (hD : D < 0) :
    (Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)) ^ 2 = (D : ℂ) := by
  have h0 : (0 : ℝ) ≤ -(D : ℝ) := by
    have : (D : ℝ) < 0 := by exact_mod_cast hD
    linarith
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt h0]
  push_cast; ring

theorem sqrt_pos_D {D : ℤ} (hD : D < 0) : 0 < Real.sqrt (-(D : ℝ)) := by
  apply Real.sqrt_pos.mpr
  have : (D : ℝ) < 0 := by exact_mod_cast hD
  linarith

theorem cmPoint_re (A B D : ℤ) : (cmPoint A B D).re = -(B : ℝ) / (2 * A) := by
  have h : (2 * (A : ℂ)) = ((2 * (A : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [cmPoint, h, Complex.div_ofReal_re]
  simp

/-- `τ_Q` is a root of `Q`. -/
theorem cmPoint_root {A B C D : ℤ} (hA : 0 < A) (hdisc : B ^ 2 - 4 * A * C = D) (hD : D < 0) :
    (A : ℂ) * cmPoint A B D ^ 2 + B * cmPoint A B D + C = 0 := by
  have hs := sqrt_sq_D hD
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hd : ((B : ℂ) ^ 2 - 4 * A * C = D) := by exact_mod_cast hdisc
  rw [cmPoint]
  field_simp
  linear_combination hs - hd

/-- The root of `Q` in the upper half plane is `τ_Q`. -/
theorem eq_cmPoint {A B C D : ℤ} (hA : 0 < A) (hdisc : B ^ 2 - 4 * A * C = D) (hD : D < 0)
    {z : ℂ} (hz : 0 < z.im) (h : (A : ℂ) * z ^ 2 + B * z + C = 0) : z = cmPoint A B D := by
  set s : ℂ := Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) with hsdef
  have hs := sqrt_sq_D hD
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hd : ((B : ℂ) ^ 2 - 4 * A * C = D) := by exact_mod_cast hdisc
  have hprod : (2 * A * z + B - s) * (2 * A * z + B + s) = 0 := by
    linear_combination 4 * (A : ℂ) * h + hd - hs
  rcases mul_eq_zero.mp hprod with h1 | h1
  · rw [cmPoint]
    field_simp
    linear_combination h1
  · exfalso
    have him := congrArg Complex.im h1
    simp [hsdef] at him
    have hApos : (0 : ℝ) < A := by exact_mod_cast hA
    have := sqrt_pos_D hD
    nlinarith

/-! ### `SL₂(ℤ)` acting on forms -/

/-- Coefficients of the form whose root is `γ • τ_Q`, `γ = [[a, b], [c, d]]`. -/
def tA (A B C _a _b c d : ℤ) : ℤ := A * d ^ 2 - B * d * c + C * c ^ 2
def tB (A B C a b c d : ℤ) : ℤ := -2 * A * b * d + B * (a * d + b * c) - 2 * C * a * c
def tC (A B C a b _c _d : ℤ) : ℤ := A * b ^ 2 - B * a * b + C * a ^ 2

theorem det_SL (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rw [Matrix.det_fin_two] at this
  exact this

section Transform

variable {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) (γ : SL(2, ℤ))

/-- shorthand -/
def A' : ℤ := tA Q.A Q.B Q.C (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
def B' : ℤ := tB Q.A Q.B Q.C (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
def C' : ℤ := tC Q.A Q.B Q.C (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)

theorem disc' : B' Q γ ^ 2 - 4 * A' Q γ * C' Q γ = D := by
  have h := det_SL γ
  have hd := Q.disc
  simp only [A', B', C', tA, tB, tC]
  linear_combination (Q.B ^ 2 - 4 * Q.A * Q.C) *
    (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 + 1) * h + hd

theorem A'_pos : 0 < A' Q γ := by
  have h := det_SL γ
  have key : 4 * Q.A * A' Q γ = (2 * Q.A * γ 1 1 - Q.B * γ 1 0) ^ 2 - D * γ 1 0 ^ 2 := by
    have hd := Q.disc
    simp only [A', tA]; linear_combination (-(γ 1 0) ^ 2) * hd
  have hA := Q.A_pos
  have hD := Q.D_neg
  have hcd : γ 1 0 ≠ 0 ∨ γ 1 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [hc.1, hc.2] at h
    simp at h
  have hpos : 0 < (2 * Q.A * γ 1 1 - Q.B * γ 1 0) ^ 2 - D * γ 1 0 ^ 2 := by
    rcases hcd with hc | hc
    · have : 0 < γ 1 0 ^ 2 := by positivity
      nlinarith [sq_nonneg (2 * Q.A * γ 1 1 - Q.B * γ 1 0)]
    · by_cases hc0 : γ 1 0 = 0
      · rw [hc0]
        have : 0 < (2 * Q.A * γ 1 1) ^ 2 := by positivity
        simpa using this
      · have : 0 < γ 1 0 ^ 2 := by positivity
        nlinarith [sq_nonneg (2 * Q.A * γ 1 1 - Q.B * γ 1 0)]
  nlinarith

theorem primitive' : Int.gcd (Int.gcd (A' Q γ) (B' Q γ)) (C' Q γ) = 1 := by
  have h := det_SL γ
  set g := Int.gcd (Int.gcd (A' Q γ) (B' Q γ)) (C' Q γ)
  have hgA : (g : ℤ) ∣ A' Q γ := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
  have hgB : (g : ℤ) ∣ B' Q γ := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
  have hgC : (g : ℤ) ∣ C' Q γ := Int.gcd_dvd_right _ _
  set a := γ 0 0; set b := γ 0 1; set c := γ 1 0; set d := γ 1 1
  have eA : Q.A = A' Q γ * a ^ 2 + B' Q γ * a * c + C' Q γ * c ^ 2 := by
    simp only [A', B', C', tA, tB, tC]
    linear_combination (-Q.A) * (a * d - b * c + 1) * h
  have eB : Q.B = 2 * A' Q γ * a * b + B' Q γ * (a * d + b * c) + 2 * C' Q γ * c * d := by
    simp only [A', B', C', tA, tB, tC]
    linear_combination (-Q.B) * (a * d - b * c + 1) * h
  have eC : Q.C = A' Q γ * b ^ 2 + B' Q γ * d * b + C' Q γ * d ^ 2 := by
    simp only [A', B', C', tA, tB, tC]
    linear_combination (-Q.C) * (a * d - b * c + 1) * h
  have hA : (g : ℤ) ∣ Q.A := by
    rw [eA]; exact dvd_add (dvd_add (dvd_mul_of_dvd_left hgA _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hgB _) _)) (dvd_mul_of_dvd_left hgC _)
  have hB : (g : ℤ) ∣ Q.B := by
    rw [eB]; exact dvd_add (dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right hgA _) _) _) (dvd_mul_of_dvd_left hgB _))
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hgC _) _) _)
  have hC : (g : ℤ) ∣ Q.C := by
    rw [eC]; exact dvd_add (dvd_add (dvd_mul_of_dvd_left hgA _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hgB _) _)) (dvd_mul_of_dvd_left hgC _)
  have h1 : g ∣ Int.gcd (Int.gcd Q.A Q.B : ℤ) Q.C :=
    Int.dvd_gcd (Int.natCast_dvd_natCast.mpr (Int.dvd_gcd hA hB)) hC
  rw [Q.primitive] at h1
  exact Nat.dvd_one.mp h1

/-- **The transformed Heegner form** (level `M`, given `M ∣ A'`), with root `γ • τ_Q`. -/
def transform (M : ℕ) (hM : (M : ℤ) ∣ A' Q γ) : HeegnerForm M D where
  A := A' Q γ
  B := B' Q γ
  C := C' Q γ
  A_pos := A'_pos Q γ
  N_dvd := hM
  disc := disc' Q γ
  D_neg := Q.D_neg
  primitive := primitive' Q γ

theorem transform_tauH (M : ℕ) (hM : (M : ℤ) ∣ A' Q γ) :
    (transform Q γ M hM).tauH = γ • Q.tauH := by
  apply UpperHalfPlane.ext
  symm
  have hτ : (Q.A : ℂ) * (Q.tauH : ℂ) ^ 2 + Q.B * (Q.tauH : ℂ) + Q.C = 0 :=
    cmPoint_root Q.A_pos Q.disc Q.D_neg
  set τ : ℂ := (Q.tauH : ℂ)
  have hdet : ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    exact_mod_cast det_SL γ
  set z : ℂ := ((γ • Q.tauH : ℍ) : ℂ) with hzdef
  set w : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ)
  have hw : w ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ Q.tauH
    simpa [UpperHalfPlane.denom, w, τ] using this
  have hzw : z * w = ((γ 0 0 : ℤ) : ℂ) * τ + (γ 0 1 : ℤ) := by
    rw [hzdef, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    exact div_mul_cancel₀ _ hw
  have hu : (((γ 1 1 : ℤ) : ℂ) * z - (γ 0 1 : ℤ)) * w = τ := by
    linear_combination ((γ 1 1 : ℤ) : ℂ) * hzw + τ * hdet
  have hv : (-((γ 1 0 : ℤ) : ℂ) * z + (γ 0 0 : ℤ)) * w = 1 := by
    linear_combination (-((γ 1 0 : ℤ) : ℂ)) * hzw + hdet
  have hroot : ((A' Q γ : ℤ) : ℂ) * z ^ 2 + (B' Q γ : ℤ) * z + (C' Q γ : ℤ) = 0 := by
    set u := ((γ 1 1 : ℤ) : ℂ) * z - (γ 0 1 : ℤ)
    set v := -((γ 1 0 : ℤ) : ℂ) * z + (γ 0 0 : ℤ)
    have e : ((A' Q γ : ℤ) : ℂ) * z ^ 2 + (B' Q γ : ℤ) * z + (C' Q γ : ℤ) =
        (Q.A : ℂ) * u ^ 2 + Q.B * u * v + Q.C * v ^ 2 := by
      simp only [A', B', C', tA, tB, tC, u, v]; push_cast; ring
    have e2 : ((A' Q γ : ℤ) : ℂ) * z ^ 2 + (B' Q γ : ℤ) * z + (C' Q γ : ℤ) = 0 ∨ w ^ 2 = 0 := by
      apply mul_eq_zero.mp
      rw [e]
      linear_combination ((Q.A : ℂ) * (u * w + τ) + Q.B * v * w) * hu +
        ((Q.B : ℂ) * τ + Q.C * (v * w + 1)) * hv + hτ
    exact e2.resolve_right (pow_ne_zero 2 hw)
  exact eq_cmPoint (A'_pos Q γ) (disc' Q γ) Q.D_neg (γ • Q.tauH).im_pos hroot

/-- For `γ ∈ Γ₀(N)` the transform keeps level `N`. -/
theorem dvd_A' (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : (N : ℤ) ∣ A' Q γ := by
  have hc : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  simp only [A', tA]
  exact dvd_add (dvd_sub (dvd_mul_of_dvd_left Q.N_dvd _)
    (dvd_mul_of_dvd_right hc _)) (dvd_mul_of_dvd_right (dvd_pow hc two_ne_zero) _)

/-- For `γ ∈ Γ₀(N)` the residue `B mod 2N` is kept. -/
theorem residue_transform (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) {β : ℤ} (hQ : HasResidue β Q) :
    HasResidue β (transform Q γ N (dvd_A' Q γ hγ)) := by
  have hc : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  have h := det_SL γ
  obtain ⟨k, hk⟩ := Q.N_dvd
  obtain ⟨m, hm⟩ := hc
  obtain ⟨r, hr⟩ := hQ
  show (2 * N : ℤ) ∣ B' Q γ - β
  refine ⟨r - k * γ 0 1 * γ 1 1 + Q.B * γ 0 1 * m - Q.C * γ 0 0 * m, ?_⟩
  simp only [B', tB]
  rw [hm] at h
  rw [hk, hm]
  linear_combination hr + Q.B * h

end Transform

/-! ### `Γ₀(N)`-equivalence is an equivalence relation -/

theorem equiv_refl {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : Gamma0Equiv Q Q :=
  ⟨1, Subgroup.one_mem _, one_smul _ _⟩

theorem equiv_symm {N : ℕ} {D : ℤ} {Q Q' : HeegnerForm N D} (h : Gamma0Equiv Q Q') :
    Gamma0Equiv Q' Q := by
  obtain ⟨γ, hγ, e⟩ := h
  exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, by rw [← e, inv_smul_smul]⟩

theorem equiv_trans {N : ℕ} {D : ℤ} {Q Q' Q'' : HeegnerForm N D} (h : Gamma0Equiv Q Q')
    (h' : Gamma0Equiv Q' Q'') : Gamma0Equiv Q Q'' := by
  obtain ⟨γ, hγ, e⟩ := h
  obtain ⟨γ', hγ', e'⟩ := h'
  exact ⟨γ' * γ, Subgroup.mul_mem _ hγ' hγ, by rw [mul_smul, e, e']⟩

/-! ### Finiteness -/

theorem form_ext {N : ℕ} {D : ℤ} {Q Q' : HeegnerForm N D} (hA : Q.A = Q'.A) (hB : Q.B = Q'.B) :
    Q = Q' := by
  have hC : Q.C = Q'.C := by
    have h1 := Q.disc
    have h2 := Q'.disc
    rw [hA, hB] at h1
    have hA0 := Q'.A_pos
    have : 4 * Q'.A * (Q.C - Q'.C) = 0 := by linear_combination h2 - h1
    have := (mul_eq_zero.mp this).resolve_left (by positivity)
    linarith
  cases Q; cases Q'
  simp only at hA hB hC
  subst hA hB hC
  rfl

theorem tauH_injective {N : ℕ} {D : ℤ} : Function.Injective (fun Q : HeegnerForm N D => Q.tauH) := by
  intro Q Q' h
  have h' : cmPoint Q.A Q.B D = cmPoint Q'.A Q'.B D := congrArg (fun z : ℍ => (z : ℂ)) h
  have him := congrArg Complex.im h'
  have hre := congrArg Complex.re h'
  rw [cmPoint_im, cmPoint_im] at him
  rw [cmPoint_re, cmPoint_re] at hre
  have hs := sqrt_pos_D Q.D_neg
  have hA0 : (0 : ℝ) < Q.A := by exact_mod_cast Q.A_pos
  have hA0' : (0 : ℝ) < Q'.A := by exact_mod_cast Q'.A_pos
  have hA : (Q.A : ℝ) = Q'.A := by
    field_simp at him
    nlinarith
  have hA' : Q.A = Q'.A := by exact_mod_cast hA
  have hB : (Q.B : ℝ) = Q'.B := by
    rw [hA] at hre
    field_simp at hre
    linarith
  exact form_ext hA' (by exact_mod_cast hB)

/-- A form whose root lies in the fundamental domain has bounded coefficients. -/
theorem bounded_of_mem_fd {M : ℕ} {D : ℤ} (R : HeegnerForm M D) (h : R.tauH ∈ 𝒟) :
    R.A ≤ -D ∧ |R.B| ≤ -D := by
  obtain ⟨hn, hr⟩ := h
  have hA0 : (0 : ℝ) < R.A := by exact_mod_cast R.A_pos
  have hre : R.tauH.re = -(R.B : ℝ) / (2 * R.A) := cmPoint_re _ _ _
  have him : R.tauH.im = Real.sqrt (-(D : ℝ)) / (2 * R.A) := cmPoint_im _ _ _
  have hD0 : (0 : ℝ) ≤ -(D : ℝ) := by
    have : (D : ℝ) < 0 := by exact_mod_cast R.D_neg
    linarith
  have hBA : |(R.B : ℝ)| ≤ R.A := by
    rw [hre, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * R.A)] at hr
    rw [div_le_iff₀ (by positivity)] at hr
    linarith
  have hns : Complex.normSq (R.tauH : ℂ) = R.tauH.re ^ 2 + R.tauH.im ^ 2 := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
  rw [hns, hre, him, div_pow, div_pow, Real.sq_sqrt hD0, neg_sq, ← add_div,
    le_div_iff₀ (by positivity)] at hn
  have hB2 : (R.B : ℝ) ^ 2 ≤ (R.A : ℝ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hBA 2
  have hA1 : (1 : ℝ) ≤ R.A := by exact_mod_cast R.A_pos
  have hAD : (R.A : ℝ) ≤ -D := by nlinarith
  have hAD' : R.A ≤ -D := by exact_mod_cast hAD
  refine ⟨hAD', ?_⟩
  have : |(R.B : ℝ)| ≤ -D := hBA.trans hAD
  exact_mod_cast this

theorem finite_bounded (M : ℕ) (D : ℤ) :
    {R : HeegnerForm M D | R.A ≤ -D ∧ |R.B| ≤ -D}.Finite := by
  let f : HeegnerForm M D → ℤ × ℤ := fun R => (R.A, R.B)
  have hf : Function.Injective f := fun R R' h => form_ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hfin : (f ⁻¹' ((Finset.Icc D (-D) ×ˢ Finset.Icc D (-D) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))).Finite :=
    Set.Finite.preimage hf.injOn (Finset.finite_toSet _)
  refine hfin.subset fun R hR => ?_
  obtain ⟨h1, h2⟩ := hR
  have := R.A_pos
  simp only [Set.mem_preimage, Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc, f]
  refine ⟨⟨by linarith, h1⟩, ?_, ?_⟩ <;> [linarith [neg_abs_le R.B]; linarith [le_abs_self R.B]]

/-- **Every Heegner form of residue `β` is `Γ₀(N)`-equivalent to one in a finite set.** -/
theorem exists_finite (N : ℕ) [NeZero N] (D β : ℤ) :
    ∃ T : Set (HeegnerForm N D), T.Finite ∧ (∀ Q ∈ T, HasResidue β Q) ∧
      ∀ Q : HeegnerForm N D, HasResidue β Q → ∃ Q' ∈ T, Gamma0Equiv Q Q' := by
  classical
  let Kset : Set SL(2, ℤ) :=
    Set.range (fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N => q.out)
  have hK : Kset.Finite := Set.finite_range _
  let Rset := {R : HeegnerForm 1 D | R.A ≤ -D ∧ |R.B| ≤ -D}
  let W : Set ℍ := Set.image2 (fun k w => k⁻¹ • w) Kset ((fun R : HeegnerForm 1 D => R.tauH) '' Rset)
  have hW : W.Finite := hK.image2 _ ((finite_bounded 1 D).image _)
  let T : Set (HeegnerForm N D) := {Q | HasResidue β Q ∧ Q.tauH ∈ W}
  refine ⟨T, ?_, fun Q hQ => hQ.1, fun Q hQ => ?_⟩
  · exact (hW.preimage tauH_injective.injOn).subset fun Q hQ => hQ.2
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd Q.tauH
  let R := transform Q g 1 (by simp)
  have hR : R.tauH = g • Q.tauH := transform_tauH Q g 1 _
  have hRb : R ∈ Rset := bounded_of_mem_fd R (hR ▸ hg)
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) g
  set k := (QuotientGroup.mk g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out with hkdef
  set γ : SL(2, ℤ) := (h : SL(2, ℤ))⁻¹ with hγdef
  have hγ : γ ∈ CongruenceSubgroup.Gamma0 N := Subgroup.inv_mem _ h.2
  have hgk : g = k * γ := by rw [hh, hγdef, mul_inv_cancel_right]
  let Q' := transform Q γ N (dvd_A' Q γ hγ)
  have hQ' : Q'.tauH = γ • Q.tauH := transform_tauH Q γ N _
  refine ⟨Q', ⟨residue_transform Q γ hγ hQ, ?_⟩, ⟨γ, hγ, hQ'.symm⟩⟩
  refine ⟨k, ⟨_, hkdef.symm⟩, R.tauH, ⟨R, hRb, rfl⟩, ?_⟩
  show k⁻¹ • R.tauH = Q'.tauH
  rw [hR, hQ', hgk, mul_smul, inv_smul_smul]

/-- **Heegner representatives exist** (glue `HeegnerRepsExist`, proved). -/
theorem exists_reps (N : ℕ) [NeZero N] (D β : ℤ) :
    ∃ S : Finset (HeegnerForm N D), IsHeegnerReps N D β S := by
  classical
  obtain ⟨T, hT, hTres, hTall⟩ := exists_finite N D β
  by_cases hne : Nonempty (HeegnerForm N D)
  swap
  · exact ⟨∅, fun Q hQ => absurd hQ (Finset.notMem_empty _), fun Q _ => absurd ⟨Q⟩ hne⟩
  let rep : HeegnerForm N D → HeegnerForm N D :=
    fun Q => Classical.epsilon (fun Q'' => Q'' ∈ T ∧ Gamma0Equiv Q Q'')
  have rep_spec : ∀ Q, (∃ Q'' ∈ T, Gamma0Equiv Q Q'') → rep Q ∈ T ∧ Gamma0Equiv Q (rep Q) := by
    intro Q hQ
    obtain ⟨Q'', h1, h2⟩ := hQ
    show Classical.epsilon _ ∈ T ∧ Gamma0Equiv Q (Classical.epsilon _)
    exact Classical.epsilon_spec (p := fun Q'' => Q'' ∈ T ∧ Gamma0Equiv Q Q'') ⟨Q'', h1, h2⟩
  have rep_congr : ∀ Q Q₁, Gamma0Equiv Q Q₁ → rep Q = rep Q₁ := by
    intro Q Q₁ h
    have : (fun Q'' => Q'' ∈ T ∧ Gamma0Equiv Q Q'') = (fun Q'' => Q'' ∈ T ∧ Gamma0Equiv Q₁ Q'') := by
      funext Q''
      apply propext
      exact ⟨fun ⟨a, b⟩ => ⟨a, equiv_trans (equiv_symm h) b⟩, fun ⟨a, b⟩ => ⟨a, equiv_trans h b⟩⟩
    show Classical.epsilon _ = Classical.epsilon _
    rw [this]
  refine ⟨hT.toFinset.image rep, ?_, ?_⟩
  · intro x hx
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hx
    rw [Set.Finite.mem_toFinset] at hQ
    exact hTres _ (rep_spec Q ⟨Q, hQ, equiv_refl Q⟩).1
  · intro Q hQ
    obtain ⟨Q₀, hQ₀, hQQ₀⟩ := hTall Q hQ
    have hs₀ := rep_spec Q₀ ⟨Q₀, hQ₀, equiv_refl Q₀⟩
    refine ⟨rep Q₀, ⟨Finset.mem_image.mpr ⟨Q₀, (Set.Finite.mem_toFinset _).mpr hQ₀, rfl⟩,
      equiv_trans hQQ₀ hs₀.2⟩, ?_⟩
    rintro Q' ⟨hQ'S, hQQ'⟩
    obtain ⟨Q₁, hQ₁, rfl⟩ := Finset.mem_image.mp hQ'S
    rw [Set.Finite.mem_toFinset] at hQ₁
    have hs₁ := rep_spec Q₁ ⟨Q₁, hQ₁, equiv_refl Q₁⟩
    apply rep_congr
    exact equiv_trans (equiv_trans hs₁.2 (equiv_symm hQQ')) hQQ₀

end Reps

end ZInQ.GZHL3
