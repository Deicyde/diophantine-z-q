import ZInQKernel.OneProof.H.LPrefix

/-! Development file for §6 of LinYangPrinted.lean: modularity of the Siegel Eisenstein series. -/

set_option linter.all false

noncomputable section

namespace HDec.HSyn.G0Split.ThetaPt.LinYangPrinted

open Matrix Complex

abbrev SpMat := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ

/-! ### Positivity of the imaginary part on complex vectors -/

/-- `v̄ᵀ (Im Ω) v` for complex `v` (written with `Ω`). -/
def qIm (Ω : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) : ℝ :=
  ∑ i, ∑ j, (Ω i j).im * ((v i).re * (v j).re + (v i).im * (v j).im)

theorem qIm_pos {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ PkgI1.SiegelH2) {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    0 < qIm Ω v := by
  obtain ⟨-, hpd⟩ := hΩ
  have hq := (posDef_iff_dotProduct_mulVec.mp hpd).2
  set a : Fin 2 → ℝ := fun i => (v i).re
  set b : Fin 2 → ℝ := fun i => (v i).im
  have ha : 0 ≤ star a ⬝ᵥ ((Ω.map Complex.im) *ᵥ a) := by
    by_cases h : a = 0
    · simp [h]
    · exact (hq h).le
  have hb : 0 ≤ star b ⬝ᵥ ((Ω.map Complex.im) *ᵥ b) := by
    by_cases h : b = 0
    · simp [h]
    · exact (hq h).le
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    apply Complex.ext
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  have key : qIm Ω v = star a ⬝ᵥ ((Ω.map Complex.im) *ᵥ a) + star b ⬝ᵥ ((Ω.map Complex.im) *ᵥ b) := by
    simp only [qIm, dotProduct, mulVec, Matrix.map_apply, star_trivial, Fin.sum_univ_two, a, b]
    ring
  rw [key]
  rcases hab with h | h
  · have := hq h; linarith
  · have := hq h; linarith

/-- `ω(u, u)` for `u = (Ωv, v)`: `star(Ωv)·(−v) + star v·(Ωv) = 2i·qIm`. -/
theorem omega_form {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ωᵀ = Ω) (v : Fin 2 → ℂ) :
    star (Ω *ᵥ v) ⬝ᵥ (-v) + star v ⬝ᵥ (Ω *ᵥ v) = 2 * Complex.I * (qIm Ω v : ℂ) := by
  have h10 : Ω 1 0 = Ω 0 1 := by
    have := congrFun (congrFun hs 0) 1; simpa using this
  apply Complex.ext <;>
    simp [qIm, dotProduct, mulVec, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, h10] <;> ring

/-! ### Symplectic invariance of `ω(a, b) = a·Jb` -/

/-- Integer matrices cast to `ℂ`. -/
abbrev cM (M : SpMat) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := M.map (Int.cast : ℤ → ℂ)

theorem cM_mul (M N : SpMat) : cM (M * N) = cM M * cM N := by
  have := Matrix.map_mul (f := Int.castRingHom ℂ) (L := M) (M := N)
  simpa using this

theorem J_map : (Matrix.J (Fin 2) ℤ).map (Int.cast : ℤ → ℂ) = Matrix.J (Fin 2) ℂ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.J, Matrix.one_apply] <;> split_ifs <;> simp

theorem sp_transpose_J {M : SpMat} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) :
    (cM M)ᵀ * Matrix.J (Fin 2) ℂ * cM M = Matrix.J (Fin 2) ℂ := by
  have h := (SymplecticGroup.mem_iff').mp hM
  have h2 := congrArg (fun X : SpMat => cM X) h
  simp only [cM_mul] at h2
  rw [← J_map]
  convert h2 using 2
  · ext i j; rfl

theorem cM_conjTranspose (M : SpMat) : (cM M)ᴴ = (cM M)ᵀ := by
  ext i j; simp [Matrix.conjTranspose_apply]

theorem bil_inv {M : SpMat} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) (a b : Fin 2 ⊕ Fin 2 → ℂ) :
    (cM M *ᵥ a) ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ (cM M *ᵥ b)) = a ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ b) := by
  calc (cM M *ᵥ a) ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ (cM M *ᵥ b))
      = a ⬝ᵥ ((cM M)ᵀ *ᵥ (Matrix.J (Fin 2) ℂ *ᵥ (cM M *ᵥ b))) := by
        rw [Matrix.mulVec_transpose, dotProduct_comm (cM M *ᵥ a), Matrix.dotProduct_mulVec, dotProduct_comm]
    _ = a ⬝ᵥ (((cM M)ᵀ * Matrix.J (Fin 2) ℂ * cM M) *ᵥ b) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = a ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ b) := by rw [sp_transpose_J hM]

theorem star_cM_mulVec (M : SpMat) (a : Fin 2 ⊕ Fin 2 → ℂ) : star (cM M *ᵥ a) = cM M *ᵥ star a := by
  rw [Matrix.star_mulVec, cM_conjTranspose, Matrix.vecMul_transpose]

theorem herm_inv {M : SpMat} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) (a b : Fin 2 ⊕ Fin 2 → ℂ) :
    star (cM M *ᵥ a) ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ (cM M *ᵥ b)) = star a ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ b) := by
  rw [star_cM_mulVec, bil_inv hM]

/-! ### Block form of `cM M` acting on `(p, q)` -/

theorem cM_mulVec_elim (M : SpMat) (p q : Fin 2 → ℂ) :
    cM M *ᵥ Sum.elim p q = Sum.elim ((cM M).toBlocks₁₁ *ᵥ p + (cM M).toBlocks₁₂ *ᵥ q)
      ((cM M).toBlocks₂₁ *ᵥ p + (cM M).toBlocks₂₂ *ᵥ q) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (cM M)]
  rw [Matrix.fromBlocks_mulVec]
  rfl

theorem J_mulVec_elim (p q : Fin 2 → ℂ) : Matrix.J (Fin 2) ℂ *ᵥ Sum.elim p q = Sum.elim (-q) p := by
  rw [Matrix.J, Matrix.fromBlocks_mulVec]
  simp [Matrix.neg_mulVec]

theorem star_elim (p q : Fin 2 → ℂ) : star (Sum.elim p q) = Sum.elim (star p) (star q) := by
  funext x; cases x <;> rfl

theorem form_elim (p q p' q' : Fin 2 → ℂ) :
    Sum.elim p q ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ Sum.elim p' q') = p ⬝ᵥ (-q') + q ⬝ᵥ p' := by
  rw [J_mulVec_elim, sumElim_dotProduct_sumElim]

/-- `W = AΩ + B`, `X = CΩ + D`. -/
def Wm (M : SpMat) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (cM M).toBlocks₁₁ * Ω + (cM M).toBlocks₁₂
def Xm (M : SpMat) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (cM M).toBlocks₂₁ * Ω + (cM M).toBlocks₂₂

theorem spFactor_eq (M : SpMat) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : PkgI1.spFactor M Ω = (Xm M Ω).det := rfl
theorem spAct_eq (M : SpMat) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : PkgI1.spAct M Ω = Wm M Ω * (Xm M Ω)⁻¹ := rfl

theorem cM_mulVec_u (M : SpMat) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    cM M *ᵥ Sum.elim (Ω *ᵥ v) v = Sum.elim (Wm M Ω *ᵥ v) (Xm M Ω *ᵥ v) := by
  rw [cM_mulVec_elim, Wm, Xm, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- The fundamental identity: `ω((Wv, Xv), (Wv, Xv)) = 2i·v̄ᵀ(Im Ω)v`. -/
theorem key_form {M : SpMat} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) {Ω : Matrix (Fin 2) (Fin 2) ℂ}
    (hs : Ωᵀ = Ω) (v : Fin 2 → ℂ) :
    star (Wm M Ω *ᵥ v) ⬝ᵥ (-(Xm M Ω *ᵥ v)) + star (Xm M Ω *ᵥ v) ⬝ᵥ (Wm M Ω *ᵥ v) =
      2 * Complex.I * (qIm Ω v : ℂ) := by
  have h := herm_inv hM (Sum.elim (Ω *ᵥ v) v) (Sum.elim (Ω *ᵥ v) v)
  rw [cM_mulVec_u, star_elim, star_elim, form_elim, form_elim] at h
  rw [h, omega_form hs v]

/-- **`det(CΩ + D) ≠ 0` on `𝔥₂` (proved).** -/
theorem spFactor_ne_zero {M : SpMat} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ PkgI1.SiegelH2) : PkgI1.spFactor M Ω ≠ 0 := by
  intro h0
  rw [spFactor_eq] at h0
  obtain ⟨v, hv, hXv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h := key_form hM hΩ.1 v
  rw [hXv] at h
  simp only [neg_zero, dotProduct_zero, star_zero, zero_dotProduct, add_zero] at h
  have hq := qIm_pos hΩ hv
  have h2 : (qIm Ω v : ℂ) = 0 := by
    have hI : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
    exact (mul_eq_zero.mp h.symm).resolve_left hI
  exact hq.ne' (by exact_mod_cast h2)

theorem isUnit_Xm {M : SpMat} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ PkgI1.SiegelH2) : IsUnit (Xm M Ω).det :=
  isUnit_iff_ne_zero.mpr (spFactor_ne_zero hM hΩ)

/-- `ω` for real `a`: `star(Za)·(−a) + star a·(Za) = 2i·aᵀ(Im Z)a`. -/
theorem real_form (Z : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 2 → ℝ) :
    star (Z *ᵥ (fun i => (a i : ℂ))) ⬝ᵥ (-(fun i => (a i : ℂ))) + star (fun i => (a i : ℂ)) ⬝ᵥ (Z *ᵥ (fun i => (a i : ℂ))) =
      2 * Complex.I * ((star a ⬝ᵥ ((Z.map Complex.im) *ᵥ a) : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [dotProduct, mulVec, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- **`Sp₄(ℤ)` preserves `𝔥₂` (proved).** -/
theorem spAct_mem {M : SpMat} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ PkgI1.SiegelH2) : PkgI1.spAct M Ω ∈ PkgI1.SiegelH2 := by
  have hX := isUnit_Xm hM hΩ
  set W := Wm M Ω
  set X := Xm M Ω
  have hZX : ∀ v, (W * X⁻¹) *ᵥ (X *ᵥ v) = W *ᵥ v := by
    intro v; rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hX, Matrix.mul_one]
  have hXX : ∀ a, X *ᵥ (X⁻¹ *ᵥ a) = a := by
    intro a; rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]
  rw [spAct_eq]
  -- symmetry from the bilinear invariance
  have hbil : ∀ v₁ v₂ : Fin 2 → ℂ, (X *ᵥ v₁) ⬝ᵥ (W *ᵥ v₂) = (W *ᵥ v₁) ⬝ᵥ (X *ᵥ v₂) := by
    intro v₁ v₂
    have h := bil_inv hM (Sum.elim (Ω *ᵥ v₁) v₁) (Sum.elim (Ω *ᵥ v₂) v₂)
    rw [cM_mulVec_u, cM_mulVec_u, form_elim, form_elim] at h
    have hs : v₁ ⬝ᵥ (Ω *ᵥ v₂) = (Ω *ᵥ v₁) ⬝ᵥ v₂ := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hΩ.1]
    rw [dotProduct_neg, dotProduct_neg, hs, neg_add_cancel] at h
    linear_combination h
  have hsym : (W * X⁻¹)ᵀ = W * X⁻¹ := by
    ext i j
    have h := hbil (X⁻¹ *ᵥ Pi.single i 1) (X⁻¹ *ᵥ Pi.single j 1)
    rw [hXX, hXX, ← hZX (X⁻¹ *ᵥ Pi.single i 1), ← hZX (X⁻¹ *ᵥ Pi.single j 1), hXX, hXX] at h
    simp [Matrix.mulVec_single, dotProduct_single, single_dotProduct] at h
    simpa [Matrix.transpose_apply] using h.symm
  refine ⟨hsym, ?_⟩
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun a ha => ?_⟩
  · ext i j
    have := congrFun (congrFun hsym j) i
    simp only [Matrix.transpose_apply] at this
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial]
    exact congrArg Complex.im this.symm
  · set ac : Fin 2 → ℂ := fun i => (a i : ℂ)
    set v := X⁻¹ *ᵥ ac
    have hv : v ≠ 0 := by
      intro h0
      apply ha
      have h1 : ac = 0 := by rw [← hXX ac]; show X *ᵥ v = 0; rw [h0, Matrix.mulVec_zero]
      funext i
      have := congrFun h1 i
      simpa [ac] using this
    have hk := key_form hM hΩ.1 v
    rw [hXX ac, ← hZX v, hXX ac] at hk
    rw [real_form] at hk
    have hI : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
    have e := mul_left_cancel₀ hI hk
    have e' : star a ⬝ᵥ ((W * X⁻¹).map Complex.im *ᵥ a) = qIm Ω v := by exact_mod_cast e
    rw [e']
    exact qIm_pos hΩ hv

end HDec.HSyn.G0Split.ThetaPt.LinYangPrinted
