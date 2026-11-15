import ZInQKernel.OneProof.H.TailZ17

/-! # OneProof H, leaf-fold12: `igusaCMValue24` proved (cm-24 value), `sixContactMin_of_open14`

cm24-value (docs/research/cm24-value.md, scratch/cm24-value/CM24Kernel.lean, copied verbatim below apart from
this header and its import) proves the added leaf `igusaCMValue24` (Lin–Yang's Igusa vector at the Baba–Granath
CM value `j = −16/27`) in Lean, with no leaf: genus-2 theta inversion from Mathlib's
`jacobiTheta₂_functional_equation`, duplication, Landen, the cubic modular equation, and a Bezout certificate.
The next generation `OpenAddedLeaves11` drops the field, and `addedLeaves10_of_open11` fills it with
`CM24.igusaCMValue24_field`. -/

/-! # cm24-value against the build: the field `igusaCMValue24` (type
`HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24`, `ZInQKernel/OneProof/H/TailZ3.lean` l.1093) proved.
Same proof as `CM24Value.lean` (which uses the verbatim qm-glue copy), here over the build's own definitions. -/

set_option linter.all false
open Complex Matrix
open scoped Real

noncomputable section

namespace CM24

/-- The general genus-2 theta term with real characteristics `c = (c0,c1)`, `d = (d0,d1)` at the symmetric
matrix `[[α, β], [β, γ]]`: `exp(πi vᵀΩv + 2πi v·d)`, `v = n + c`. -/
def term2 (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (n : ℤ × ℤ) : ℂ :=
  cexp (π * I * (α * (((n.1 : ℝ) + c0 : ℝ) : ℂ) ^ 2 + 2 * β * (((n.1 : ℝ) + c0 : ℝ) : ℂ) * (((n.2 : ℝ) + c1 : ℝ) : ℂ)
      + γ * (((n.2 : ℝ) + c1 : ℝ) : ℂ) ^ 2)
    + 2 * π * I * ((((n.1 : ℝ) + c0 : ℝ) : ℂ) * d0 + (((n.2 : ℝ) + c1 : ℝ) : ℂ) * d1))

def Th2 (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) : ℂ := ∑' n : ℤ × ℤ, term2 α β γ c0 c1 d0 d1 n

theorem re_exponent (α β γ : ℂ) (x y d0 d1 : ℝ) :
    (π * I * (α * (x : ℂ) ^ 2 + 2 * β * x * y + γ * (y : ℂ) ^ 2) + 2 * π * I * ((x : ℂ) * d0 + (y : ℂ) * d1)).re
      = -π * (α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2) := by
  simp [Complex.mul_re, Complex.mul_im, pow_two]

/-- 1D Gaussian summability. -/
theorem summable_gauss {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    Summable (fun n : ℤ => Real.exp (-π * δ * ((n : ℝ) + c) ^ 2)) := by
  have h := ((summable_jacobiTheta₂_term_iff ((c * δ : ℝ) * I) ((δ : ℂ) * I)).2
    (by simpa using hδ)).norm.mul_left (Real.exp (-π * δ * c ^ 2))
  refine h.congr fun n => ?_
  rw [norm_jacobiTheta₂_term, ← Real.exp_add]
  congr 1
  simp
  ring

theorem norm_term2 (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (n : ℤ × ℤ) :
    ‖term2 α β γ c0 c1 d0 d1 n‖ = Real.exp (-π * (α.im * ((n.1 : ℝ) + c0) ^ 2
      + 2 * β.im * ((n.1 : ℝ) + c0) * ((n.2 : ℝ) + c1) + γ.im * ((n.2 : ℝ) + c1) ^ 2)) := by
  rw [term2, Complex.norm_exp, re_exponent]

theorem summable_norm_term2 {α β γ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hQ : ∀ x y : ℝ, δ * (x ^ 2 + y ^ 2) ≤ α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2)
    (c0 c1 d0 d1 : ℝ) : Summable (fun n => ‖term2 α β γ c0 c1 d0 d1 n‖) := by
  have h := (summable_gauss hδ c0).mul_of_nonneg (summable_gauss hδ c1)
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) h
  rw [norm_term2, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have := hQ ((n.1 : ℝ) + c0) ((n.2 : ℝ) + c1)
  nlinarith [Real.pi_pos]

theorem summable_term2 {α β γ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hQ : ∀ x y : ℝ, δ * (x ^ 2 + y ^ 2) ≤ α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2)
    (c0 c1 d0 d1 : ℝ) : Summable (term2 α β γ c0 c1 d0 d1) :=
  (summable_norm_term2 hδ hQ c0 c1 d0 d1).of_norm


/-- Sum over `ℤ × ℤ` as an iterated sum, inner over the first coordinate. -/
theorem tsum_swap_iter {f : ℤ × ℤ → ℂ} (hf : Summable f) :
    ∑' n, f n = ∑' n1 : ℤ, ∑' n0 : ℤ, f (n0, n1) := by
  rw [← (Equiv.prodComm ℤ ℤ).tsum_eq]
  exact ((Equiv.prodComm ℤ ℤ).summable_iff.2 hf).tsum_prod

theorem term2_eq_jt (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (n0 n1 : ℤ) :
    term2 α β γ c0 c1 d0 d1 (n0, n1) =
      cexp (π * I * (α * (c0 : ℂ) ^ 2 + 2 * β * c0 * ((n1 : ℂ) + c1) + γ * ((n1 : ℂ) + c1) ^ 2)
        + 2 * π * I * ((c0 : ℂ) * d0 + ((n1 : ℂ) + c1) * d1)) *
      jacobiTheta₂_term n0 (c0 * α + β * ((n1 : ℂ) + c1) + d0) α := by
  rw [term2, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem jt_dual (α β γ : ℂ) (hα : α ≠ 0) (c0 c1 d0 d1 : ℝ) (m n1 : ℤ) :
    cexp (π * I * (α * (c0 : ℂ) ^ 2 + 2 * β * c0 * ((n1 : ℂ) + c1) + γ * ((n1 : ℂ) + c1) ^ 2)
        + 2 * π * I * ((c0 : ℂ) * d0 + ((n1 : ℂ) + c1) * d1)) *
      (cexp (-π * I * (c0 * α + β * ((n1 : ℂ) + c1) + d0) ^ 2 / α) *
        jacobiTheta₂_term m ((c0 * α + β * ((n1 : ℂ) + c1) + d0) / α) (-1 / α)) =
      cexp (2 * π * I * c0 * d0) * term2 (-1 / α) (β / α) (γ - β ^ 2 / α) (-d0) c1 c0 d1 (m, n1) := by
  rw [term2, jacobiTheta₂_term, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- **Partial inversion in the first coordinate** (two applications of Mathlib's
`jacobiTheta₂_functional_equation` give the full inversion `Ω ↦ −Ω⁻¹`). -/
theorem pi0 {α β γ : ℂ} (hα : 0 < α.im) (c0 c1 d0 d1 : ℝ)
    (hs : Summable (term2 α β γ c0 c1 d0 d1))
    (hs' : Summable (term2 (-1 / α) (β / α) (γ - β ^ 2 / α) (-d0) c1 c0 d1)) :
    Th2 α β γ c0 c1 d0 d1 = 1 / (-I * α) ^ (1 / 2 : ℂ) * cexp (2 * π * I * c0 * d0) *
      Th2 (-1 / α) (β / α) (γ - β ^ 2 / α) (-d0) c1 c0 d1 := by
  have hα0 : α ≠ 0 := fun h => by simp [h] at hα
  rw [Th2, Th2, tsum_swap_iter hs, tsum_swap_iter hs', ← tsum_mul_left]
  congr 1; funext n1
  conv_lhs => enter [1]; ext n0; rw [term2_eq_jt]
  rw [tsum_mul_left]
  change _ * jacobiTheta₂ _ _ = _
  rw [jacobiTheta₂_functional_equation, jacobiTheta₂, ← tsum_mul_left, ← tsum_mul_left,
    ← tsum_mul_left]
  congr 1; funext m
  conv_rhs => rw [mul_assoc, ← jt_dual α β γ hα0 c0 c1 d0 d1 m n1]
  ring


/-! ## Symmetries -/

theorem th2_swap (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) : Th2 α β γ c0 c1 d0 d1 = Th2 γ β α c1 c0 d1 d0 := by
  rw [Th2, Th2, ← (Equiv.prodComm ℤ ℤ).tsum_eq]
  congr 1; funext n
  simp only [term2, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  congr 1; ring

theorem th2_shift_c (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (k0 k1 : ℤ) :
    Th2 α β γ (c0 + k0) (c1 + k1) d0 d1 = Th2 α β γ c0 c1 d0 d1 := by
  rw [Th2, Th2]
  conv_rhs => rw [← (Equiv.addRight ((k0, k1) : ℤ × ℤ)).tsum_eq]
  congr 1; funext n
  simp only [term2, Equiv.coe_addRight, Prod.fst_add, Prod.snd_add]
  congr 1; push_cast; ring

theorem th2_shift_d (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (k0 k1 : ℤ) :
    Th2 α β γ c0 c1 (d0 + k0) (d1 + k1) =
      cexp (2 * π * I * (c0 * k0 + c1 * k1)) * Th2 α β γ c0 c1 d0 d1 := by
  rw [Th2, Th2, ← tsum_mul_left]
  congr 1; funext n
  have h : cexp (((-(n.1 * k0 + n.2 * k1) : ℤ) : ℂ) * (2 * π * I)) = 1 := exp_int_mul_two_pi_mul_I _
  rw [term2, term2, ← mul_one (cexp (_ + _)), ← h, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

/-! ## Duplication -/

/-- `(σ, p, q) ↦ (p + q + σ, p − q)`, a bijection `Fin 2 × ℤ × ℤ ≃ ℤ × ℤ`. -/
def dupE1 : Fin 2 × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun w := (w.2.1 + w.2.2 + (w.1 : ℕ), w.2.1 - w.2.2)
  invFun mn := (if (mn.1 - mn.2) % 2 = 0 then 0 else 1,
    (mn.2 + (mn.1 - mn.2 - (if (mn.1 - mn.2) % 2 = 0 then 0 else 1)) / 2,
     (mn.1 - mn.2 - (if (mn.1 - mn.2) % 2 = 0 then 0 else 1)) / 2))
  left_inv w := by
    obtain ⟨σ, p, q⟩ := w
    fin_cases σ <;> simp <;> omega
  right_inv mn := by
    obtain ⟨m, n⟩ := mn
    by_cases h : (m - n) % 2 = 0 <;> simp [h] <;> omega

/-- The 2D version: `((σ₀,σ₁), (p, q)) ↦ (p + q + σ, p − q)` on `ℤ² × ℤ²`. -/
def dupE2 : (Fin 2 × Fin 2) × ((ℤ × ℤ) × (ℤ × ℤ)) ≃ (ℤ × ℤ) × (ℤ × ℤ) where
  toFun w := ((w.2.1.1 + w.2.2.1 + (w.1.1 : ℕ), w.2.1.2 + w.2.2.2 + (w.1.2 : ℕ)),
    (w.2.1.1 - w.2.2.1, w.2.1.2 - w.2.2.2))
  invFun mn :=
    let s0 : ℤ := if (mn.1.1 - mn.2.1) % 2 = 0 then 0 else 1
    let s1 : ℤ := if (mn.1.2 - mn.2.2) % 2 = 0 then 0 else 1
    ((if (mn.1.1 - mn.2.1) % 2 = 0 then 0 else 1, if (mn.1.2 - mn.2.2) % 2 = 0 then 0 else 1),
      ((mn.2.1 + (mn.1.1 - mn.2.1 - s0) / 2, mn.2.2 + (mn.1.2 - mn.2.2 - s1) / 2),
       ((mn.1.1 - mn.2.1 - s0) / 2, (mn.1.2 - mn.2.2 - s1) / 2)))
  left_inv w := by
    obtain ⟨⟨σ0, σ1⟩, ⟨p0, p1⟩, ⟨q0, q1⟩⟩ := w
    fin_cases σ0 <;> fin_cases σ1 <;> simp <;> omega
  right_inv mn := by
    obtain ⟨⟨m0, m1⟩, ⟨n0, n1⟩⟩ := mn
    by_cases h0 : (m0 - n0) % 2 = 0 <;> by_cases h1 : (m1 - n1) % 2 = 0 <;> simp [h0, h1] <;> omega

theorem dupE2_apply (σ0 σ1 : Fin 2) (p0 p1 q0 q1 : ℤ) :
    dupE2 ((σ0, σ1), ((p0, p1), (q0, q1))) =
      ((p0 + q0 + (σ0 : ℕ), p1 + q1 + (σ1 : ℕ)), (p0 - q0, p1 - q1)) := rfl

theorem dup2 {α β γ : ℂ} (c0 c1 d0 d1 : ℝ)
    (hs : Summable (fun n => ‖term2 α β γ c0 c1 d0 d1 n‖))
    (hs2 : ∀ c0' c1' d0' d1' : ℝ, Summable (fun n => ‖term2 (2 * α) (2 * β) (2 * γ) c0' c1' d0' d1' n‖)) :
    Th2 α β γ c0 c1 d0 d1 ^ 2 = ∑ σ : Fin 2 × Fin 2,
      Th2 (2 * α) (2 * β) (2 * γ) (((σ.1 : ℕ) : ℝ) / 2 + c0) (((σ.2 : ℕ) : ℝ) / 2 + c1) (2 * d0) (2 * d1) *
      Th2 (2 * α) (2 * β) (2 * γ) (((σ.1 : ℕ) : ℝ) / 2) (((σ.2 : ℕ) : ℝ) / 2) 0 0 := by
  have hprod := summable_mul_of_summable_norm hs hs
  have h2 : Summable (fun c => term2 α β γ c0 c1 d0 d1 (dupE2 c).1 *
      term2 α β γ c0 c1 d0 d1 (dupE2 c).2) := dupE2.summable_iff.2 hprod
  rw [sq, Th2, tsum_mul_tsum_of_summable_norm hs hs, ← dupE2.tsum_eq, h2.tsum_prod, tsum_fintype]
  congr 1; funext σ
  rw [Th2, Th2, tsum_mul_tsum_of_summable_norm (hs2 _ _ _ _) (hs2 _ _ _ _)]
  congr 1; funext w
  obtain ⟨σ0, σ1⟩ := σ
  obtain ⟨⟨p0, p1⟩, ⟨q0, q1⟩⟩ := w
  rw [dupE2_apply]
  simp only [term2, ← Complex.exp_add]
  congr 1; push_cast; ring


/-! ## Genus one -/

/-- Genus-1 theta term with real characteristic: `exp(πiτ(n+c)² + 2πi(n+c)d)`. -/
def term1 (τ : ℂ) (c d : ℝ) (n : ℤ) : ℂ :=
  cexp (π * I * τ * (((n : ℝ) + c : ℝ) : ℂ) ^ 2 + 2 * π * I * (((n : ℝ) + c : ℝ) : ℂ) * d)

def th1 (τ : ℂ) (c d : ℝ) : ℂ := ∑' n : ℤ, term1 τ c d n

theorem term1_eq (τ : ℂ) (c d : ℝ) (n : ℤ) :
    term1 τ c d n = cexp (π * I * τ * (c : ℂ) ^ 2 + 2 * π * I * c * d) *
      jacobiTheta₂_term n (c * τ + d) τ := by
  rw [term1, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- The bridge to Mathlib: `th1 τ c d = exp(πiτc² + 2πicd)·jacobiTheta₂(cτ + d, τ)`. -/
theorem th1_eq (τ : ℂ) (c d : ℝ) :
    th1 τ c d = cexp (π * I * τ * (c : ℂ) ^ 2 + 2 * π * I * c * d) * jacobiTheta₂ (c * τ + d) τ := by
  rw [th1, jacobiTheta₂, ← tsum_mul_left]
  exact tsum_congr fun n => term1_eq τ c d n

theorem summable_norm_term1 {τ : ℂ} (hτ : 0 < τ.im) (c d : ℝ) :
    Summable (fun n => ‖term1 τ c d n‖) := by
  have h := ((summable_jacobiTheta₂_term_iff (c * τ + d) τ).2 hτ).norm.mul_left
    ‖cexp (π * I * τ * (c : ℂ) ^ 2 + 2 * π * I * c * d)‖
  refine h.congr fun n => ?_
  rw [term1_eq, norm_mul]

theorem th1_shift_c (τ : ℂ) (c d : ℝ) (k : ℤ) : th1 τ (c + k) d = th1 τ c d := by
  rw [th1, th1]
  conv_rhs => rw [← (Equiv.addRight k).tsum_eq]
  congr 1; funext n
  simp only [term1, Equiv.coe_addRight]
  congr 1; push_cast; ring

theorem th1_shift_d (τ : ℂ) (c d : ℝ) (k : ℤ) :
    th1 τ c (d + k) = cexp (2 * π * I * c * k) * th1 τ c d := by
  rw [th1, th1, ← tsum_mul_left]
  congr 1; funext n
  have h : cexp (((-(n * k)) : ℤ) * (2 * π * I)) = 1 := exp_int_mul_two_pi_mul_I _
  rw [term1, term1, ← mul_one (cexp (_ + _)), ← h, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem dup1 {τ : ℂ} (hτ : 0 < τ.im) (c d : ℝ) :
    th1 τ c d ^ 2 = ∑ σ : Fin 2,
      th1 (2 * τ) (((σ : ℕ) : ℝ) / 2 + c) (2 * d) * th1 (2 * τ) (((σ : ℕ) : ℝ) / 2) 0 := by
  have hs := summable_norm_term1 hτ c d
  have hτ2 : 0 < (2 * τ).im := by simpa using hτ
  have hprod := summable_mul_of_summable_norm hs hs
  have h2 : Summable (fun c' => term1 τ c d (dupE1 c').1 * term1 τ c d (dupE1 c').2) :=
    dupE1.summable_iff.2 hprod
  rw [sq, th1, tsum_mul_tsum_of_summable_norm hs hs, ← dupE1.tsum_eq, h2.tsum_prod, tsum_fintype]
  congr 1; funext σ
  rw [th1, th1, tsum_mul_tsum_of_summable_norm (summable_norm_term1 hτ2 _ _)
    (summable_norm_term1 hτ2 _ _)]
  congr 1; funext w
  obtain ⟨p, q⟩ := w
  simp only [dupE1, Equiv.coe_fn_mk, term1, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- Diagonal period matrices: the genus-2 theta factors. -/
theorem th2_diag {τ0 τ1 : ℂ} (h0 : 0 < τ0.im) (h1 : 0 < τ1.im) (c0 c1 d0 d1 : ℝ) :
    Th2 τ0 0 τ1 c0 c1 d0 d1 = th1 τ0 c0 d0 * th1 τ1 c1 d1 := by
  rw [th1, th1, tsum_mul_tsum_of_summable_norm (summable_norm_term1 h0 _ _)
    (summable_norm_term1 h1 _ _), Th2]
  congr 1; funext n
  simp only [term2, term1, ← Complex.exp_add]
  congr 1; ring

/-- The odd genus-1 theta constant vanishes. -/
theorem th1_odd (τ : ℂ) : th1 τ (1 / 2) (1 / 2) = 0 := by
  have h : th1 τ (1 / 2) (1 / 2) = -th1 τ (1 / 2) (1 / 2) := by
    conv_lhs => rw [th1, ← (Equiv.neg ℤ).tsum_eq, ← (Equiv.addRight (1 : ℤ)).tsum_eq]
    rw [th1, ← tsum_neg]
    congr 1; funext n
    simp only [term1, Equiv.coe_addRight, Equiv.neg_apply]
    have : π * I * τ * (((((-(n + 1) : ℤ) : ℝ) + 1 / 2 : ℝ)) : ℂ) ^ 2
        + 2 * π * I * (((((-(n + 1) : ℤ) : ℝ) + 1 / 2 : ℝ)) : ℂ) * ((1 / 2 : ℝ) : ℂ) =
        (π * I * τ * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ 2 + 2 * π * I * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ))
          + ((-n - 1 : ℤ) : ℂ) * (2 * π * I) + π * I := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_add, exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
    ring
  have : (2 : ℂ) * th1 τ (1 / 2) (1 / 2) = 0 := by linear_combination h
  simpa using this


/-! ## The explicit matrices: `Ω₂₄`, its partial inversion, and `W = −Ω₂₄⁻¹` -/

abbrev r6 : ℝ := √6
theorem r6_sq : r6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
theorem r6_pos : 0 < r6 := Real.sqrt_pos.2 (by norm_num)

/-- `Ω₂₄ = [[α0, β0], [β0, γ0]]`. -/
def α0 : ℂ := ⟨-2 / 7, 3 * r6 / 14⟩
def β0 : ℂ := ⟨-1 / 7, -r6 / 7⟩
def γ0 : ℂ := ⟨-4 / 7, 3 * r6 / 7⟩
/-- The partial inversion `[[−1/α0, β0/α0], [β0/α0, γ0 − β0²/α0]]`. -/
def α1 : ℂ := ⟨4 / 5, 3 * r6 / 5⟩
def β1 : ℂ := ⟨-2 / 5, r6 / 5⟩
def γ1 : ℂ := ⟨-4 / 5, 2 * r6 / 5⟩
/-- `W = −Ω₂₄⁻¹ = [[wa, wb], [wb, wc]] = [[1 + i√6/2, 1/2], [1/2, 1/2 + i√6/4]]`. -/
def wa : ℂ := ⟨1, r6 / 2⟩
def wb : ℂ := ⟨1 / 2, 0⟩
def wc : ℂ := ⟨1 / 2, r6 / 4⟩

theorem α0_ne : α0 ≠ 0 := fun h => by
  have := congrArg Complex.im h; simp [α0] at this <;> linarith [r6_pos]
theorem γ1_ne : γ1 ≠ 0 := fun h => by
  have := congrArg Complex.im h; simp [γ1] at this <;> linarith [r6_pos]

theorem eqA1 : -1 / α0 = α1 := by
  rw [div_eq_iff α0_ne]; apply Complex.ext <;> simp [α0, α1] <;> nlinarith [r6_sq]
theorem eqB1 : β0 / α0 = β1 := by
  rw [div_eq_iff α0_ne]; apply Complex.ext <;> simp [α0, β0, β1] <;> nlinarith [r6_sq]
theorem eqC1 : γ0 - β0 ^ 2 / α0 = γ1 := by
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', eq_div_iff α0_ne]
  apply Complex.ext <;> simp [α0, β0, γ0, γ1, pow_two] <;> nlinarith [r6_sq]
theorem eqA2 : -1 / γ1 = wc := by
  rw [div_eq_iff γ1_ne]; apply Complex.ext <;> simp [γ1, wc] <;> nlinarith [r6_sq]
theorem eqB2 : β1 / γ1 = wb := by
  rw [div_eq_iff γ1_ne]; apply Complex.ext <;> simp [γ1, β1, wb] <;> nlinarith [r6_sq]
theorem eqC2 : α1 - β1 ^ 2 / γ1 = wa := by
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', eq_div_iff γ1_ne]
  apply Complex.ext <;> simp [α1, β1, γ1, wa, pow_two] <;> nlinarith [r6_sq]

theorem pos0 : ∀ x y : ℝ, r6 / 7 * (x ^ 2 + y ^ 2) ≤
    α0.im * x ^ 2 + 2 * β0.im * x * y + γ0.im * y ^ 2 := by
  intro x y; simp only [α0, β0, γ0]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg (x - 2 * y))]
theorem pos1 : ∀ x y : ℝ, r6 / 5 * (x ^ 2 + y ^ 2) ≤
    α1.im * x ^ 2 + 2 * β1.im * x * y + γ1.im * y ^ 2 := by
  intro x y; simp only [α1, β1, γ1]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg x), mul_nonneg r6_pos.le (sq_nonneg (x + y))]
theorem pos1s : ∀ x y : ℝ, r6 / 5 * (x ^ 2 + y ^ 2) ≤
    γ1.im * x ^ 2 + 2 * β1.im * x * y + α1.im * y ^ 2 := by
  intro x y; simp only [α1, β1, γ1]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg y), mul_nonneg r6_pos.le (sq_nonneg (x + y))]
theorem posW : ∀ x y : ℝ, r6 / 4 * (x ^ 2 + y ^ 2) ≤
    wa.im * x ^ 2 + 2 * wb.im * x * y + wc.im * y ^ 2 := by
  intro x y; simp only [wa, wb, wc]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg x)]
theorem posW2 : ∀ x y : ℝ, r6 / 2 * (x ^ 2 + y ^ 2) ≤
    (2 * wa).im * x ^ 2 + 2 * (2 * wb).im * x * y + (2 * wc).im * y ^ 2 := by
  intro x y; simp [wa, wb, wc]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg x)]
theorem posWs : ∀ x y : ℝ, r6 / 4 * (x ^ 2 + y ^ 2) ≤
    wc.im * x ^ 2 + 2 * wb.im * x * y + wa.im * y ^ 2 := by
  intro x y; simp only [wa, wb, wc]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg y)]

theorem d0pos : (0 : ℝ) < r6 / 7 := div_pos r6_pos (by norm_num)
theorem d1pos : (0 : ℝ) < r6 / 5 := div_pos r6_pos (by norm_num)
theorem d2pos : (0 : ℝ) < r6 / 4 := div_pos r6_pos (by norm_num)
theorem d3pos : (0 : ℝ) < r6 / 2 := div_pos r6_pos (by norm_num)

/-- **The inversion `Ω₂₄ ↦ W`** on theta constants with characteristics: two partial inversions
(each Mathlib's one-variable functional equation) and two coordinate swaps. -/
theorem invert (a0 a1 : ℝ) (b0 b1 : ℤ) :
    Th2 α0 β0 γ0 (a0 / 2) (a1 / 2) ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) =
      1 / (-I * α0) ^ (1 / 2 : ℂ) * cexp (2 * π * I * (a0 / 2 : ℝ) * ((b0 : ℝ) / 2 : ℝ)) *
      (1 / (-I * γ1) ^ (1 / 2 : ℂ) * cexp (2 * π * I * (a1 / 2 : ℝ) * ((b1 : ℝ) / 2 : ℝ))) *
      Th2 wa wb wc ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) (a0 / 2) (a1 / 2) := by
  have hα : 0 < α0.im := by simp [α0] <;> exact r6_pos
  have hγ : 0 < γ1.im := by simp [γ1] <;> exact r6_pos
  rw [pi0 hα _ _ _ _ (summable_term2 d0pos pos0 _ _ _ _)
    (by rw [eqA1, eqB1, eqC1]; exact summable_term2 d1pos pos1 _ _ _ _), eqA1, eqB1, eqC1,
    th2_swap, pi0 hγ _ _ _ _ (summable_term2 d1pos pos1s _ _ _ _)
    (by rw [eqA2, eqB2, eqC2]; exact summable_term2 d2pos posWs _ _ _ _), eqA2, eqB2, eqC2,
    th2_swap]
  have e0 : ((b0 : ℝ) / 2) = -((b0 : ℝ) / 2) + (b0 : ℤ) := by ring
  have e1 : ((b1 : ℝ) / 2) = -((b1 : ℝ) / 2) + (b1 : ℤ) := by ring
  conv_rhs => rw [e0, e1, th2_shift_c]
  ring_nf


/-! ## `2W = diag(i√6, i√6/2) + [[2,1],[1,1]]`: translation to a diagonal matrix -/

/-- `τ₆ = i√6`, `τ₃ = i√6/2`: the two CM points of discriminant `−24` (one per ideal class). -/
def τ6 : ℂ := ⟨0, r6⟩
def τ3 : ℂ := ⟨0, r6 / 2⟩

theorem τ6_im : 0 < τ6.im := by simp [τ6] <;> exact r6_pos
theorem τ3_im : 0 < τ3.im := by simp [τ3] <;> exact div_pos r6_pos (by norm_num)

theorem h2wa : 2 * wa = τ6 + 2 := by apply Complex.ext <;> simp [wa, τ6] <;> ring
theorem h2wb : 2 * wb = 1 := by apply Complex.ext <;> simp [wb]
theorem h2wc : 2 * wc = τ3 + 1 := by apply Complex.ext <;> simp [wc, τ3] <;> ring

theorem th2_phase {α β γ α' β' γ' : ℂ} {c0 c1 d0 d1 d0' d1' : ℝ} (κ : ℂ)
    (h : ∀ n : ℤ × ℤ, ∃ k : ℤ,
      π * I * (α * (((n.1 : ℝ) + c0 : ℝ) : ℂ) ^ 2 + 2 * β * (((n.1 : ℝ) + c0 : ℝ) : ℂ) * (((n.2 : ℝ) + c1 : ℝ) : ℂ)
        + γ * (((n.2 : ℝ) + c1 : ℝ) : ℂ) ^ 2)
        + 2 * π * I * ((((n.1 : ℝ) + c0 : ℝ) : ℂ) * d0 + (((n.2 : ℝ) + c1 : ℝ) : ℂ) * d1) =
      (π * I * (α' * (((n.1 : ℝ) + c0 : ℝ) : ℂ) ^ 2 + 2 * β' * (((n.1 : ℝ) + c0 : ℝ) : ℂ) * (((n.2 : ℝ) + c1 : ℝ) : ℂ)
        + γ' * (((n.2 : ℝ) + c1 : ℝ) : ℂ) ^ 2)
        + 2 * π * I * ((((n.1 : ℝ) + c0 : ℝ) : ℂ) * d0' + (((n.2 : ℝ) + c1 : ℝ) : ℂ) * d1'))
        + κ + k * (2 * π * I)) :
    Th2 α β γ c0 c1 d0 d1 = cexp κ * Th2 α' β' γ' c0 c1 d0' d1' := by
  rw [Th2, Th2, ← tsum_mul_left]
  congr 1; funext n
  obtain ⟨k, hk⟩ := h n
  rw [term2, hk, Complex.exp_add, Complex.exp_add, exp_int_mul_two_pi_mul_I, term2]
  ring

theorem cast_even (n : ℤ) : ∃ t : ℤ, ((n : ℂ) * (n + 1)) = t + t := by
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self n
  exact ⟨t, by exact_mod_cast ht⟩

/-- `U(c) = θ[c; 0](2W)` for `c ∈ {0, 1/2}²`. -/
def U (c0 c1 : ℝ) : ℂ := Th2 (2 * wa) (2 * wb) (2 * wc) c0 c1 0 0

theorem U00 : U 0 0 = th1 τ6 0 0 * th1 τ3 0 (1 / 2) := by
  rw [U, th2_phase (α' := τ6) (β' := 0) (γ' := τ3) (d0' := 0) (d1' := 1 / 2) 0, th2_diag τ6_im τ3_im]
  · simp
  intro n
  obtain ⟨t, ht⟩ := cast_even (n.2 - 1)
  refine ⟨n.1 ^ 2 + n.1 * n.2 + t, ?_⟩
  rw [h2wa, h2wb, h2wc]; push_cast at ht ⊢
  linear_combination (π * I) * ht

theorem U10 : U (1 / 2) 0 = I * (th1 τ6 (1 / 2) 0 * th1 τ3 0 0) := by
  rw [U, th2_phase (α' := τ6) (β' := 0) (γ' := τ3) (d0' := 0) (d1' := 0) (π * I / 2),
    th2_diag τ6_im τ3_im]
  · congr 1
    rw [show (π : ℂ) * I / 2 = π / 2 * I by ring, Complex.exp_mul_I]
    have h1 : Complex.cos (π / 2) = 0 := by exact_mod_cast Real.cos_pi_div_two
    have h2 : Complex.sin (π / 2) = 1 := by exact_mod_cast Real.sin_pi_div_two
    rw [h1, h2]; ring
  intro n
  obtain ⟨t, ht⟩ := cast_even n.2
  refine ⟨n.1 ^ 2 + n.1 + n.1 * n.2 + t, ?_⟩
  rw [h2wa, h2wb, h2wc]; push_cast at ht ⊢
  linear_combination (π * I) * ht

theorem U01 : U 0 (1 / 2) = cexp (π * I / 4) * (th1 τ6 0 (1 / 2) * th1 τ3 (1 / 2) 0) := by
  rw [U, th2_phase (α' := τ6) (β' := 0) (γ' := τ3) (d0' := 1 / 2) (d1' := 0) (π * I / 4),
    th2_diag τ6_im τ3_im]
  intro n
  obtain ⟨t, ht⟩ := cast_even n.2
  refine ⟨n.1 ^ 2 + n.1 * n.2 + t, ?_⟩
  rw [h2wa, h2wb, h2wc]; push_cast at ht ⊢
  linear_combination (π * I) * ht

theorem U11 : U (1 / 2) (1 / 2) = 0 := by
  rw [U, th2_phase (α' := τ6) (β' := 0) (γ' := τ3) (d0' := 1 / 2) (d1' := 1 / 2) (π * I / 4),
    th2_diag τ6_im τ3_im, th1_odd]
  · simp
  intro n
  obtain ⟨t, ht⟩ := cast_even n.2
  refine ⟨n.1 ^ 2 + n.1 * n.2 + n.1 + t, ?_⟩
  rw [h2wa, h2wb, h2wc]; push_cast at ht ⊢
  linear_combination (π * I) * ht

/-! ## The cubic modular equation `θ₃(τ)θ₃(3τ) = θ₂(τ)θ₂(3τ) + θ₄(τ)θ₄(3τ)` -/

/-- `(ε, r, s) ↦ (r + s + ε, r − s)`. -/
def cubE1 : Fin 2 × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun w := (w.2.1 + w.2.2 + (w.1 : ℕ), w.2.1 - w.2.2)
  invFun mn := (if (mn.1 + mn.2) % 2 = 0 then 0 else 1,
    ((mn.1 + mn.2 - (if (mn.1 + mn.2) % 2 = 0 then 0 else 1)) / 2,
     (mn.1 + mn.2 - (if (mn.1 + mn.2) % 2 = 0 then 0 else 1)) / 2 - mn.2))
  left_inv w := by
    obtain ⟨σ, p, q⟩ := w
    fin_cases σ <;> simp <;> omega
  right_inv mn := by
    obtain ⟨m, n⟩ := mn
    by_cases h : (m + n) % 2 = 0 <;> simp [h] <;> omega

/-- `(ε, r, s) ↦ (2r − s + ε, s)`. -/
def cubE2 : Fin 2 × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun w := (2 * w.2.1 - w.2.2 + (w.1 : ℕ), w.2.2)
  invFun uv := (if (uv.1 + uv.2) % 2 = 0 then 0 else 1,
    ((uv.1 + uv.2 - (if (uv.1 + uv.2) % 2 = 0 then 0 else 1)) / 2, uv.2))
  left_inv w := by
    obtain ⟨σ, p, q⟩ := w
    fin_cases σ <;> simp <;> omega
  right_inv uv := by
    obtain ⟨u, v⟩ := uv
    by_cases h : (u + v) % 2 = 0 <;> simp [h] <;> omega

/-- `(r, s) ↦ (r − s, −1 − s)`. -/
def cubE3 : ℤ × ℤ ≃ ℤ × ℤ where
  toFun w := (w.1 - w.2, -1 - w.2)
  invFun w := (w.1 - 1 - w.2, -1 - w.2)
  left_inv w := by obtain ⟨r, s⟩ := w; simp <;> omega
  right_inv w := by obtain ⟨r, s⟩ := w; simp <;> omega

theorem cubic {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 0 * th1 (3 * τ) 0 0 =
      th1 τ (1 / 2) 0 * th1 (3 * τ) (1 / 2) 0 + th1 τ 0 (1 / 2) * th1 (3 * τ) 0 (1 / 2) := by
  have h3 : 0 < (3 * τ).im := by simp; linarith
  have hQ : ∀ x y : ℝ, τ.im * (x ^ 2 + y ^ 2) ≤ τ.im * x ^ 2 + 2 * (0 : ℂ).im * x * y + (3 * τ).im * y ^ 2 := by
    intro x y; simp; nlinarith [sq_nonneg y]
  rw [← th2_diag hτ h3, ← th2_diag hτ h3, ← th2_diag hτ h3]
  set F := term2 τ 0 (3 * τ) 0 0 0 0
  set G := term2 τ 0 (3 * τ) 0 0 (1 / 2) (1 / 2)
  set H := term2 τ 0 (3 * τ) (1 / 2) (1 / 2) 0 0
  have hF : Summable F := summable_term2 hτ hQ _ _ _ _
  have hG : Summable G := summable_term2 hτ hQ _ _ _ _
  have hH : Summable H := summable_term2 hτ hQ _ _ _ _
  -- the phase: `G(m,n) = (−1)^{m+n} F(m,n)`
  have hGF : ∀ m n : ℤ, G (m, n) = cexp (((m + n : ℤ) : ℂ) * (π * I)) * F (m, n) := by
    intro m n
    simp only [G, F, term2, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hev : ∀ r s : ℤ, G (r + s, r - s) = F (r + s, r - s) := by
    intro r s
    rw [hGF, show (((r + s + (r - s) : ℤ) : ℂ) * (π * I)) = ((r : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      exp_int_mul_two_pi_mul_I, one_mul]
  have hod : ∀ r s : ℤ, G (r + s + 1, r - s) = -F (r + s + 1, r - s) := by
    intro r s
    rw [hGF, show (((r + s + 1 + (r - s) : ℤ) : ℂ) * (π * I)) = ((r : ℤ) : ℂ) * (2 * π * I) + π * I by
      push_cast; ring, Complex.exp_add, exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
    ring
  have hFH : ∀ r s : ℤ, F (r + s + 1, r - s) = H (2 * r - s, s) := by
    intro r s
    simp only [F, H, term2]
    congr 1; push_cast; ring
  have hHH : ∀ r s : ℤ, H (2 * r - s + 1, s) = H (2 * (r - s) - (-1 - s), -1 - s) := by
    intro r s
    simp only [H, term2]
    congr 1; push_cast; ring
  -- LHS − θ₄θ₄' = 2 Σ F(r+s+1, r−s)
  have hL : Th2 τ 0 (3 * τ) 0 0 0 0 - Th2 τ 0 (3 * τ) 0 0 (1 / 2) (1 / 2) =
      2 * ∑' w : ℤ × ℤ, F (w.1 + w.2 + 1, w.1 - w.2) := by
    rw [Th2, Th2, ← hF.tsum_sub hG]
    have hs : Summable (fun w => (F - G) (cubE1 w)) := cubE1.summable_iff.2 (hF.sub hG)
    rw [show (fun n => F n - G n) = (F - G) from rfl, ← cubE1.tsum_eq, hs.tsum_prod, tsum_fintype,
      Fin.sum_univ_two, ← tsum_mul_left]
    have h0 : ∀ w : ℤ × ℤ, (F - G) (cubE1 (0, w)) = 0 := by
      intro w; simp only [cubE1, Equiv.coe_fn_mk, Pi.sub_apply, Fin.val_zero, Nat.cast_zero, add_zero]
      rw [hev]; ring
    have h1 : ∀ w : ℤ × ℤ, (F - G) (cubE1 (1, w)) = 2 * F (w.1 + w.2 + 1, w.1 - w.2) := by
      intro w; simp only [cubE1, Equiv.coe_fn_mk, Pi.sub_apply, Fin.val_one, Nat.cast_one]
      rw [hod]; ring
    simp only [h0, h1, tsum_zero, zero_add]
  have hR : Th2 τ 0 (3 * τ) (1 / 2) (1 / 2) 0 0 = 2 * ∑' w : ℤ × ℤ, H (2 * w.1 - w.2, w.2) := by
    rw [Th2]
    have hs : Summable (fun w => H (cubE2 w)) := cubE2.summable_iff.2 hH
    rw [← cubE2.tsum_eq, hs.tsum_prod, tsum_fintype, Fin.sum_univ_two]
    have h1 : ∑' w : ℤ × ℤ, H (cubE2 (1, w)) = ∑' w : ℤ × ℤ, H (2 * w.1 - w.2, w.2) := by
      simp only [cubE2, Equiv.coe_fn_mk, Fin.val_one, Nat.cast_one]
      conv_rhs => rw [← cubE3.tsum_eq]
      congr 1; funext w
      simp only [cubE3, Equiv.coe_fn_mk]
      exact hHH w.1 w.2
    rw [h1]
    simp only [cubE2, Equiv.coe_fn_mk, Fin.val_zero, Nat.cast_zero, add_zero]
    ring
  have hLR : ∑' w : ℤ × ℤ, F (w.1 + w.2 + 1, w.1 - w.2) = ∑' w : ℤ × ℤ, H (2 * w.1 - w.2, w.2) :=
    tsum_congr fun w => hFH w.1 w.2
  linear_combination hL - hR + 2 * hLR

end CM24

namespace CM24Alg

/-- The minimal polynomial of `k₆ = (2−√3)(√3−√2)`. -/
def mpoly (k : ℂ) : ℂ := k ^ 4 + 12 * k ^ 3 + 2 * k ^ 2 - 12 * k + 1

/-- `S/4` in `x, y, Z₂ = z²`. -/
def Sp (x y Z2 : ℂ) : ℂ := 4 * (Z2 ^ 2 + 14 * Z2 * x ^ 2 + 14 * Z2 * y ^ 2 + x ^ 4 + 14 * x ^ 2 * y ^ 2 + y ^ 4)
/-- `P²` in `x, y, Z₂`. -/
def Pp (x y Z2 : ℂ) : ℂ :=
  4096 * x ^ 4 * y ^ 4 * Z2 ^ 2 * ((x ^ 2 - 2 * x * y + y ^ 2 - Z2) * (x ^ 2 + 2 * x * y + y ^ 2 - Z2)) ^ 2

theorem core (k : ℂ) (hm : mpoly k = 0) :
    3779136 * Pp (1 - k) (-k * (1 + k)) (-4 * k * (1 - k ^ 2)) =
      -16 / 27 * Sp (1 - k) (-k * (1 + k)) (-4 * k * (1 - k ^ 2)) ^ 5 := by
  unfold mpoly at hm; unfold Pp Sp
  linear_combination (16384*k^36/27 + 524288*k^35/3 + 60588032*k^34/3 + 1175977984*k^33 + 105139945472*k^32/3 + 1394766512128*k^31/3 + 18405419909120*k^30/9 + 20264252342272*k^29/3 + 19946604396544*k^28/3 - 13769320169472*k^27 - 146141425565696*k^26/3 - 119603788251136*k^25/3 + 720511197446144*k^24/9 + 507636047937536*k^23/3 - 71685357961216*k^22/3 - 283984371122176*k^21 - 260222024187904*k^20/3 + 985619954139136*k^19/3 + 3810450640928768*k^18/27 - 985619954139136*k^17/3 - 260222024187904*k^16/3 + 283984371122176*k^15 - 71685357961216*k^14/3 - 507636047937536*k^13/3 + 720511197446144*k^12/9 + 119603788251136*k^11/3 - 146141425565696*k^10/3 + 13769320169472*k^9 + 19946604396544*k^8/3 - 20264252342272*k^7/3 + 18405419909120*k^6/9 - 1394766512128*k^5/3 + 105139945472*k^4/3 - 1175977984*k^3 + 60588032*k^2/3 - 524288*k/3 + 16384/27) * hm

theorem core_ne (k : ℂ) (hm : mpoly k = 0) : Sp (1 - k) (-k * (1 + k)) (-4 * k * (1 - k ^ 2)) ≠ 0 := by
  unfold mpoly at hm
  have h : (5*k^3/768 + 271*k^2/3456 + 37*k/2304 - 191/2304) * Sp (1 - k) (-k * (1 + k)) (-4 * k * (1 - k ^ 2)) = 1 := by
    unfold Sp; linear_combination -(-5*k^7/192 - 1351*k^6/864 - 251*k^5/64 - 2815*k^4/1728 + 1453*k^3/192 + 943*k^2/432 - 2293*k/576 + 767/576) * hm
  exact right_ne_zero_of_mul_eq_one h

/-- `k₆ = (2−√3)(√3−√2)` is a root of `mpoly`. -/
theorem mpoly_k6 (a b : ℂ) (ha : a ^ 2 = 2) (hb : b ^ 2 = 3) : mpoly ((2 - b) * (b - a)) = 0 := by
  unfold mpoly
  linear_combination (a^2*b^4 - 8*a^2*b^3 + 24*a^2*b^2 - 32*a^2*b + 16*a^2 - 4*a*b^5 + 32*a*b^4 - 84*a*b^3 + 56*a*b^2 + 80*a*b - 96*a + 6*b^6 - 48*b^5 + 110*b^4 + 8*b^3 - 286*b^2 + 216*b + 40) * ha + (-4*a*b^5 + 32*a*b^4 - 80*a*b^3 + 72*a*b^2 - 44*a*b + 56*a + b^6 - 8*b^5 + 27*b^4 - 80*b^3 + 175*b^2 - 136*b - 27) * hb

end CM24Alg

namespace CM24
open HDec.LeafQCheck.HM.QMSplit.Value24

/-! ## Bridge to `PkgI1.thetaConst` -/

theorem thetaConst_eq (m : HDec.PkgI1.Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : Ω 1 0 = Ω 0 1) :
    HDec.PkgI1.thetaConst m Ω = Th2 (Ω 0 0) (Ω 0 1) (Ω 1 1) (((m.1 0 : ℕ) : ℝ) / 2) (((m.1 1 : ℕ) : ℝ) / 2)
      (((m.2 0 : ℕ) : ℝ) / 2) (((m.2 1 : ℕ) : ℝ) / 2) := by
  rw [HDec.PkgI1.thetaConst, Th2, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  congr 1; funext p
  simp only [finTwoArrowEquiv_symm_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, term2,
    Matrix.cons_val_zero, Matrix.cons_val_one, hΩ]
  congr 1; push_cast; ring

theorem om24_00 : Om24 0 0 = α0 := by
  apply Complex.ext <;> simp [Om24, α0] <;> ring
theorem om24_01 : Om24 0 1 = β0 := by
  apply Complex.ext <;> simp [Om24, β0] <;> ring
theorem om24_10 : Om24 1 0 = β0 := by
  apply Complex.ext <;> simp [Om24, β0] <;> ring
theorem om24_11 : Om24 1 1 = γ0 := by
  apply Complex.ext <;> simp [Om24, γ0] <;> ring


/-! ## Squares of theta constants at `Ω₂₄` in terms of `U` -/

/-- `𝓔 = 1/((−iα0)(−iγ1))`: the square of the two automorphy factors. -/
def Ecal : ℂ := 1 / (-I * α0) * (1 / (-I * γ1))

theorem cpow_half_sq (x : ℂ) : (1 / x ^ (1 / 2 : ℂ)) ^ 2 = 1 / x := by
  rw [div_pow, one_pow, show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num, Complex.cpow_nat_inv_pow x two_ne_zero]

theorem sq_inv (a0 a1 b0 b1 : ℕ) :
    Th2 α0 β0 γ0 ((a0 : ℝ) / 2) ((a1 : ℝ) / 2) ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) ^ 2 =
      Ecal * cexp (π * I * ((a0 * b0 + a1 * b1 : ℕ) : ℂ)) *
        Th2 wa wb wc ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) ((a0 : ℝ) / 2) ((a1 : ℝ) / 2) ^ 2 := by
  have h := invert (a0 : ℝ) (a1 : ℝ) (b0 : ℤ) (b1 : ℤ)
  simp only [Int.cast_natCast] at h
  have e1 : cexp (2 * π * I * ((a0 : ℝ) / 2 : ℝ) * ((b0 : ℝ) / 2 : ℝ)) ^ 2 *
      cexp (2 * π * I * ((a1 : ℝ) / 2 : ℝ) * ((b1 : ℝ) / 2 : ℝ)) ^ 2 =
      cexp (π * I * ((a0 * b0 + a1 * b1 : ℕ) : ℂ)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [h]
  simp only [mul_pow]
  rw [cpow_half_sq, cpow_half_sq, ← e1, Ecal]
  ring

/-- `U` with characteristic reduced mod `ℤ²`. -/
def Uf (s0 s1 : ℕ) : ℂ := U (((s0 % 2 : ℕ) : ℝ) / 2) (((s1 % 2 : ℕ) : ℝ) / 2)

theorem U_nat (s0 s1 : ℕ) : U ((s0 : ℝ) / 2) ((s1 : ℝ) / 2) = Uf s0 s1 := by
  rw [Uf, U, U]
  conv_rhs => rw [← th2_shift_c _ _ _ _ _ _ _ ((s0 / 2 : ℕ) : ℤ) ((s1 / 2 : ℕ) : ℤ)]
  simp only [Int.cast_natCast]
  have h0 : (s0 : ℝ) = ((s0 % 2 : ℕ) : ℝ) + 2 * ((s0 / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div s0 2).symm
  have h1 : (s1 : ℝ) = ((s1 % 2 : ℕ) : ℝ) + 2 * ((s1 / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div s1 2).symm
  congr 1 <;> linarith

theorem exp_pi_nat (k : ℕ) : cexp (π * I * (k : ℂ)) = (-1) ^ k := by
  rw [mul_comm, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- **Duplication at `W`, with the translation reductions.** -/
theorem sqW (a0 a1 b0 b1 : ℕ) :
    Th2 wa wb wc ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) ((a0 : ℝ) / 2) ((a1 : ℝ) / 2) ^ 2 =
      ∑ σ : Fin 2 × Fin 2, (-1 : ℂ) ^ (((σ.1 : ℕ) + b0) * a0 + ((σ.2 : ℕ) + b1) * a1) *
        Uf ((σ.1 : ℕ) + b0) ((σ.2 : ℕ) + b1) * Uf σ.1 σ.2 := by
  rw [dup2 _ _ _ _ (summable_norm_term2 d2pos posW _ _ _ _)
    (fun _ _ _ _ => summable_norm_term2 d3pos posW2 _ _ _ _)]
  congr 1; funext σ
  have e0 : 2 * ((a0 : ℝ) / 2) = 0 + ((a0 : ℤ) : ℝ) := by push_cast; ring
  have e1 : 2 * ((a1 : ℝ) / 2) = 0 + ((a1 : ℤ) : ℝ) := by push_cast; ring
  rw [e0, e1, th2_shift_d]
  have c0 : ((σ.1 : ℕ) : ℝ) / 2 + (b0 : ℝ) / 2 = (((σ.1 : ℕ) + b0 : ℕ) : ℝ) / 2 := by push_cast; ring
  have c1 : ((σ.2 : ℕ) : ℝ) / 2 + (b1 : ℝ) / 2 = (((σ.2 : ℕ) + b1 : ℕ) : ℝ) / 2 := by push_cast; ring
  rw [c0, c1]
  change _ * U _ _ * U _ _ = _
  rw [U_nat, U_nat, ← exp_pi_nat]
  congr 2
  congr 1; push_cast; ring

theorem om24_sym : Om24 1 0 = Om24 0 1 := by rw [om24_10, om24_01]

theorem sq_char (m : HDec.PkgI1.Char2) :
    HDec.PkgI1.thetaConst m Om24 ^ 2 =
      Ecal * cexp (π * I * (((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ) : ℕ) : ℂ)) *
      ∑ σ : Fin 2 × Fin 2, (-1 : ℂ) ^ (((σ.1 : ℕ) + (m.2 0 : ℕ)) * (m.1 0 : ℕ) + ((σ.2 : ℕ) + (m.2 1 : ℕ)) * (m.1 1 : ℕ)) *
        Uf ((σ.1 : ℕ) + (m.2 0 : ℕ)) ((σ.2 : ℕ) + (m.2 1 : ℕ)) * Uf σ.1 σ.2 := by
  rw [thetaConst_eq m Om24 om24_sym, om24_00, om24_01, om24_11, sq_inv, sqW]

theorem U11' : U (1 / 2) (1 / 2) = 0 := U11
theorem U11'' : U 2⁻¹ 2⁻¹ = 0 := by rw [← one_div]; exact U11

theorem exp_pi_two : cexp (π * I * 2) = 1 := by
  rw [show (π : ℂ) * I * 2 = ((1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring, exp_int_mul_two_pi_mul_I]

theorem sqc0 : HDec.PkgI1.thetaConst (![0, 0], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 + U (1 / 2) 0 ^ 2 + U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc1 : HDec.PkgI1.thetaConst (![0, 1], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 + U (1 / 2) 0 ^ 2 - U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc2 : HDec.PkgI1.thetaConst (![1, 0], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 - U (1 / 2) 0 ^ 2 + U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc3 : HDec.PkgI1.thetaConst (![1, 1], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 - U (1 / 2) 0 ^ 2 - U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc4 : HDec.PkgI1.thetaConst (![0, 0], ![1, 0]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U (1 / 2) 0) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc5 : HDec.PkgI1.thetaConst (![0, 1], ![1, 0]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U (1 / 2) 0) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc6 : HDec.PkgI1.thetaConst (![0, 0], ![0, 1]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U 0 (1 / 2)) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc7 : HDec.PkgI1.thetaConst (![1, 0], ![0, 1]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U 0 (1 / 2)) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc8 : HDec.PkgI1.thetaConst (![0, 0], ![1, 1]) Om24 ^ 2 =
    Ecal * (2 * U 0 (1 / 2) * U (1 / 2) 0) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc9 : HDec.PkgI1.thetaConst (![1, 1], ![1, 1]) Om24 ^ 2 =
    Ecal * (-(2 * U 0 (1 / 2) * U (1 / 2) 0)) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

/-! ## Genus one: duplication (Landen) and Jacobi's identity -/

theorem th1_c1 (τ : ℂ) (d : ℝ) : th1 τ 1 d = th1 τ 0 d := by
  simpa using th1_shift_c τ 0 d 1

theorem th1_d1 (τ : ℂ) (c : ℝ) : th1 τ c 1 = cexp (2 * π * I * c) * th1 τ c 0 := by
  simpa using th1_shift_d τ c 0 1

theorem exp_half : cexp (2 * π * I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
  rw [show (2 : ℂ) * π * I * ((1 / 2 : ℝ) : ℂ) = π * I by push_cast; ring, Complex.exp_pi_mul_I]

theorem dupA {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 0 ^ 2 = th1 (2 * τ) 0 0 ^ 2 + th1 (2 * τ) (1 / 2) 0 ^ 2 := by
  rw [dup1 hτ, Fin.sum_univ_two]; norm_num; ring

theorem dupB {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 (1 / 2) ^ 2 = th1 (2 * τ) 0 0 ^ 2 - th1 (2 * τ) (1 / 2) 0 ^ 2 := by
  rw [dup1 hτ, Fin.sum_univ_two]
  have e : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  simp only [e, th1_d1, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_div, zero_add,
    add_zero, exp_half]
  push_cast; simp only [mul_zero, Complex.exp_zero]; ring

theorem dupC {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ (1 / 2) 0 ^ 2 = 2 * th1 (2 * τ) 0 0 * th1 (2 * τ) (1 / 2) 0 := by
  rw [dup1 hτ, Fin.sum_univ_two]
  have e : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_div, zero_add, mul_zero, e, th1_c1]
  ring

/-- **Jacobi's quartic identity** `θ₀₀⁴ = θ₀₁⁴ + θ₁₀⁴`, from the duplication formulas. -/
theorem jacobi {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 0 ^ 4 = th1 τ 0 (1 / 2) ^ 4 + th1 τ (1 / 2) 0 ^ 4 := by
  have hA := dupA hτ; have hB := dupB hτ; have hC := dupC hτ
  linear_combination (th1 τ 0 0 ^ 2 + th1 (2 * τ) 0 0 ^ 2 + th1 (2 * τ) (1 / 2) 0 ^ 2) * hA
    - (th1 τ 0 (1 / 2) ^ 2 + th1 (2 * τ) 0 0 ^ 2 - th1 (2 * τ) (1 / 2) 0 ^ 2) * hB
    - (th1 τ (1 / 2) 0 ^ 2 + 2 * th1 (2 * τ) 0 0 * th1 (2 * τ) (1 / 2) 0) * hC

theorem h2τ3 : 2 * τ3 = τ6 := by apply Complex.ext <;> simp [τ3, τ6] <;> ring

/-! ## The leaf: the singular modulus `k₆` -/

end CM24

/-- **The singular modulus `k₆`** (Weber, Ramanujan; disc `−24`; first used here as an intermediate leaf,
now PROVED below as `CM24.singularModulus6`, so it is not needed). With Mathlib's `jacobiTheta₂`,
`θ₃(τ) = jacobiTheta₂ 0 τ = Σ exp(πin²τ)` and `θ₂(τ) = exp(πiτ/4)·jacobiTheta₂ (τ/2) τ = Σ exp(πi(n+½)²τ)`,
at `τ = i√6` (nome `q = e^{−π√6}`): `θ₃(i√6) ≠ 0` and `k₆ = θ₂(i√6)²/θ₃(i√6)² = (2−√3)(√3−√2)`.

Published form: the singular modulus `k_n = λ*(n)` of the elliptic integral (`K'(k_n)/K(k_n) = √n`, and
`k = θ₂²/θ₃²` with `q = e^{−π√n}`, Jacobi) at `n = 6`: `λ*(6) = (2−√3)(√3−√2)`. Sources (locators
UNVERIFIED, from memory): J. M. Borwein and P. B. Borwein, *Pi and the AGM* (Wiley 1987), Table 4.6 (singular
values `λ*(n)`) and Thm 2.3/§2.6 for `k = θ₂²/θ₃²`; B. C. Berndt, *Ramanujan's Notebooks Part V*, Ch. 34
(class invariants `g₆`, `G₆` and the modulus); H. Weber, *Lehrbuch der Algebra* III (1908), §§ 125-127 and the
table of class invariants. Numerically VERIFIED (`py/split.py`, 30 digits). -/
def SingularModulus6 : Prop :=
  jacobiTheta₂ 0 (I * ((√6 : ℝ) : ℂ)) ≠ 0 ∧
    (cexp (π * I * (I * ((√6 : ℝ) : ℂ)) / 4) * jacobiTheta₂ (I * ((√6 : ℝ) : ℂ) / 2) (I * ((√6 : ℝ) : ℂ))) ^ 2 =
      (((2 - √3) * (√3 - √2) : ℝ) : ℂ) * jacobiTheta₂ 0 (I * ((√6 : ℝ) : ℂ)) ^ 2

namespace CM24
open HDec.LeafQCheck.HM.QMSplit.Value24

theorem τ6_eq : τ6 = I * ((√6 : ℝ) : ℂ) := by apply Complex.ext <;> simp [τ6]

theorem A0_eq : th1 τ6 0 0 = jacobiTheta₂ 0 (I * ((√6 : ℝ) : ℂ)) := by
  rw [th1_eq, τ6_eq]; simp

theorem A2_eq : th1 τ6 (1 / 2) 0 =
    cexp (π * I * (I * ((√6 : ℝ) : ℂ)) / 4) * jacobiTheta₂ (I * ((√6 : ℝ) : ℂ) / 2) (I * ((√6 : ℝ) : ℂ)) := by
  rw [th1_eq, τ6_eq]
  congr 1
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring


/-! ## Final assembly -/

theorem evenChars_eq : HDec.PkgI1.evenChars =
    {(![0, 0], ![0, 0]), (![0, 1], ![0, 0]), (![1, 0], ![0, 0]), (![1, 1], ![0, 0]), (![0, 0], ![1, 0]),
     (![0, 1], ![1, 0]), (![0, 0], ![0, 1]), (![1, 0], ![0, 1]), (![0, 0], ![1, 1]), (![1, 1], ![1, 1])} := by
  decide

theorem Ecal_ne : Ecal ≠ 0 := by
  unfold Ecal
  have h1 : -I * α0 ≠ 0 := mul_ne_zero (by simp) α0_ne
  have h2 : -I * γ1 ≠ 0 := mul_ne_zero (by simp) γ1_ne
  exact mul_ne_zero (one_div_ne_zero h1) (one_div_ne_zero h2)

theorem zeta_sq : cexp (π * I / 4) ^ 2 = I := by
  rw [← Complex.exp_nat_mul, show ((2 : ℕ) : ℂ) * (π * I / 4) = π / 2 * I by push_cast; ring, Complex.exp_mul_I]
  have h1 : Complex.cos (π / 2) = 0 := by exact_mod_cast Real.cos_pi_div_two
  have h2 : Complex.sin (π / 2) = 1 := by exact_mod_cast Real.sin_pi_div_two
  rw [h1, h2]; ring

theorem sum8 : HDec.PkgI1.thetaSum8 Om24 = Ecal ^ 4 *
    CM24Alg.Sp (U 0 0 ^ 2) (U (1 / 2) 0 ^ 2) ((U 0 (1 / 2) ^ 2) ^ 2) := by
  rw [HDec.PkgI1.thetaSum8, evenChars_eq]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  simp only [show ∀ x : ℂ, x ^ 8 = (x ^ 2) ^ 4 from fun x => by ring, sqc0, sqc1, sqc2, sqc3, sqc4, sqc5,
    sqc6, sqc7, sqc8, sqc9]
  unfold CM24Alg.Sp; ring

theorem prod2 : HDec.PkgI1.thetaProd2 Om24 ^ 2 = Ecal ^ 20 *
    CM24Alg.Pp (U 0 0 ^ 2) (U (1 / 2) 0 ^ 2) ((U 0 (1 / 2) ^ 2) ^ 2) := by
  rw [HDec.PkgI1.thetaProd2, evenChars_eq]
  simp (disch := decide) only [Finset.prod_insert, Finset.prod_singleton]
  simp only [sqc0, sqc1, sqc2, sqc3, sqc4, sqc5, sqc6, sqc7, sqc8, sqc9]
  unfold CM24Alg.Pp; ring

/-- **Core: the closed numeric statement from `mpoly(θ₁₀(i√6)²/θ₀₀(i√6)²) = 0`.** -/
theorem thetaValueAtOmega24_of_mpoly (k : ℂ) (hA0' : th1 τ6 0 0 ≠ 0)
    (hk' : th1 τ6 (1 / 2) 0 ^ 2 = k * th1 τ6 0 0 ^ 2) (hm : CM24Alg.mpoly k = 0) : ThetaValueAtOmega24 := by
  set A0 := th1 τ6 0 0
  set A1 := th1 τ6 0 (1 / 2)
  set A2 := th1 τ6 (1 / 2) 0
  set B0 := th1 τ3 0 0
  set B1 := th1 τ3 0 (1 / 2)
  set B2 := th1 τ3 (1 / 2) 0
  have rB0 : B0 ^ 2 = A0 ^ 2 + A2 ^ 2 := by have := dupA τ3_im; rw [h2τ3] at this; exact this
  have rB1 : B1 ^ 2 = A0 ^ 2 - A2 ^ 2 := by have := dupB τ3_im; rw [h2τ3] at this; exact this
  have rB2 : B2 ^ 2 = 2 * A0 * A2 := by have := dupC τ3_im; rw [h2τ3] at this; exact this
  have rJ : A0 ^ 4 = A1 ^ 4 + A2 ^ 4 := jacobi τ6_im
  have hk : A2 ^ 2 = k * A0 ^ 2 := hk'
  have hζ := zeta_sq
  set ζ := cexp (π * I / 4)
  have hx : U 0 0 ^ 2 = A0 ^ 4 * (1 - k) := by
    rw [U00]; linear_combination A0 ^ 2 * rB1 - A0 ^ 2 * hk
  have hy : U (1 / 2) 0 ^ 2 = A0 ^ 4 * (-k * (1 + k)) := by
    rw [U10]; linear_combination (A2 ^ 2 * B0 ^ 2) * I_sq - A2 ^ 2 * rB0 - (A0 ^ 2 + A2 ^ 2 + k * A0 ^ 2) * hk
  have hz : (U 0 (1 / 2) ^ 2) ^ 2 = A0 ^ 8 * (-4 * k * (1 - k ^ 2)) := by
    rw [U01]
    linear_combination (ζ ^ 2 + I) * A1 ^ 4 * B2 ^ 4 * hζ + A1 ^ 4 * B2 ^ 4 * I_sq
      - A1 ^ 4 * (B2 ^ 2 + 2 * A0 * A2) * rB2 + 4 * A0 ^ 2 * A2 ^ 2 * rJ
      + (-4 * A0 ^ 6 + 4 * A0 ^ 2 * (A2 ^ 4 + k * A0 ^ 2 * A2 ^ 2 + k ^ 2 * A0 ^ 4)) * hk
  have hS : HDec.PkgI1.thetaSum8 Om24 = Ecal ^ 4 * A0 ^ 16 *
      CM24Alg.Sp (1 - k) (-k * (1 + k)) (-4 * k * (1 - k ^ 2)) := by
    rw [sum8, hx, hy, hz]; unfold CM24Alg.Sp; ring
  have hP : HDec.PkgI1.thetaProd2 Om24 ^ 2 = Ecal ^ 20 * A0 ^ 80 *
      CM24Alg.Pp (1 - k) (-k * (1 + k)) (-4 * k * (1 - k ^ 2)) := by
    rw [prod2, hx, hy, hz]; unfold CM24Alg.Pp; ring
  have hS0 : HDec.PkgI1.thetaSum8 Om24 ≠ 0 := by
    rw [hS]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ Ecal_ne) (pow_ne_zero _ hA0')) (CM24Alg.core_ne k hm)
  have hD : HDec.PkgI1.jDen Om24 ≠ 0 := pow_ne_zero _ hS0
  refine ⟨hD, ?_⟩
  rw [div_eq_iff hD, HDec.PkgI1.jNum, HDec.PkgI1.jDen, hP, hS]
  have := CM24Alg.core k hm
  linear_combination (Ecal ^ 20 * A0 ^ 80) * this

/-- **Main theorem (leaf form): the closed numeric statement from the singular modulus `k₆`.** -/
theorem thetaValueAtOmega24_of_singularModulus6 (h : SingularModulus6) : ThetaValueAtOmega24 := by
  obtain ⟨hA0', hk'⟩ := h
  rw [← A0_eq] at hA0' hk'
  rw [← A2_eq] at hk'
  refine thetaValueAtOmega24_of_mpoly _ hA0' hk' ?_
  have ha : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hb : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have := CM24Alg.mpoly_k6 _ _ ha hb
  push_cast; exact this

/-! ## Removing the leaf: `mpoly(k) = 0` from the cubic modular equation -/

/-- The `S`-transformation of the three theta constants (Mathlib's functional equation). -/
theorem sA {τ : ℂ} : th1 τ 0 0 = 1 / (-I * τ) ^ (1 / 2 : ℂ) * th1 (-1 / τ) 0 0 := by
  rw [th1_eq, th1_eq, jacobiTheta₂_functional_equation]; simp

theorem sB {τ : ℂ} (hτ : τ ≠ 0) : th1 τ 0 (1 / 2) = 1 / (-I * τ) ^ (1 / 2 : ℂ) * th1 (-1 / τ) (1 / 2) 0 := by
  rw [th1_eq, th1_eq, jacobiTheta₂_functional_equation]
  have e : ((1 / 2 : ℝ) : ℂ) * (-1 / τ) + ((0 : ℝ) : ℂ) = -((((0 : ℝ) : ℂ) * τ + ((1 / 2 : ℝ) : ℂ)) / τ) := by
    field_simp; push_cast; ring
  rw [e, jacobiTheta₂_neg_left]
  have e2 : cexp (π * I * (-1 / τ) * ((1 / 2 : ℝ) : ℂ) ^ 2 + 2 * π * I * ((1 / 2 : ℝ) : ℂ) * ((0 : ℝ) : ℂ)) =
      cexp (-π * I * (((0 : ℝ) : ℂ) * τ + ((1 / 2 : ℝ) : ℂ)) ^ 2 / τ) := by
    congr 1; push_cast; field_simp; ring
  rw [e2]; simp; ring

theorem sC {τ : ℂ} (hτ : τ ≠ 0) : th1 τ (1 / 2) 0 = 1 / (-I * τ) ^ (1 / 2 : ℂ) * th1 (-1 / τ) 0 (1 / 2) := by
  rw [th1_eq, th1_eq, jacobiTheta₂_functional_equation]
  have e : (((1 / 2 : ℝ) : ℂ) * τ + ((0 : ℝ) : ℂ)) / τ = ((0 : ℝ) : ℂ) * (-1 / τ) + ((1 / 2 : ℝ) : ℂ) := by
    field_simp; push_cast; ring
  rw [e]
  have e2 : cexp (π * I * τ * ((1 / 2 : ℝ) : ℂ) ^ 2 + 2 * π * I * ((1 / 2 : ℝ) : ℂ) * ((0 : ℝ) : ℂ)) *
      cexp (-π * I * (((1 / 2 : ℝ) : ℂ) * τ + ((0 : ℝ) : ℂ)) ^ 2 / τ) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; push_cast; field_simp; ring
  have e3 : cexp (π * I * (-1 / τ) * ((0 : ℝ) : ℂ) ^ 2 + 2 * π * I * ((0 : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ)) = 1 := by
    simp
  rw [e3]
  linear_combination (1 / (-I * τ) ^ (1 / 2 : ℂ) *
    jacobiTheta₂ (((0 : ℝ) : ℂ) * (-1 / τ) + ((1 / 2 : ℝ) : ℂ)) (-1 / τ)) * e2

/-- On the imaginary axis `th1 (it) c 0` is the real sum `Σ exp(−πt(n+c)²)`. -/
theorem th1_imag (t c : ℝ) :
    th1 (I * t) c 0 = ((∑' n : ℤ, Real.exp (-π * t * ((n : ℝ) + c) ^ 2) : ℝ) : ℂ) := by
  rw [th1, Complex.ofReal_tsum]
  congr 1; funext n
  rw [term1, Complex.ofReal_exp]
  congr 1; push_cast; ring_nf; rw [I_sq]; ring

theorem th1_imag_pos {t : ℝ} (ht : 0 < t) (c : ℝ) : 0 < ∑' n : ℤ, Real.exp (-π * t * ((n : ℝ) + c) ^ 2) :=
  (summable_gauss ht c).tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- `τ' = i√6/3 = −1/τ₃`, `3τ' = τ₆`. -/
def τp : ℂ := I * ((r6 / 3 : ℝ) : ℂ)

theorem τ3_ne : τ3 ≠ 0 := fun h => by
  have := congrArg Complex.im h; simp [τ3] at this <;> linarith [r6_pos]
theorem τp_eq : -1 / τ3 = τp := by
  rw [div_eq_iff τ3_ne]; apply Complex.ext <;> simp [τ3, τp] <;> nlinarith [r6_sq]
theorem τp_im : 0 < τp.im := by simp [τp] <;> exact div_pos r6_pos (by norm_num)
theorem h3τp : 3 * τp = τ6 := by apply Complex.ext <;> simp [τp, τ6] <;> ring
theorem τ6_eq' : τ6 = I * ((r6 : ℝ) : ℂ) := by apply Complex.ext <;> simp [τ6]

/-- `K = 1/(−iτ₃)^{1/2}` is a positive real. -/
theorem K_real : 1 / (-I * τ3) ^ (1 / 2 : ℂ) = (((1 / (r6 / 2) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have e : -I * τ3 = ((r6 / 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [τ3]
  rw [e, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (div_pos r6_pos (by norm_num)).le]
  push_cast; ring
theorem K_pos : (0 : ℝ) < 1 / (r6 / 2) ^ (1 / 2 : ℝ) :=
  div_pos one_pos (Real.rpow_pos_of_pos (div_pos r6_pos (by norm_num)) _)

/-- **`mpoly(θ₁₀(i√6)²/θ₀₀(i√6)²) = 0`** (no leaf): cubic modular equation at `τ'`, `S`, Landen, Jacobi. -/
theorem mpoly_A (A0 A1 A2 B0 B1 B2 : ℂ) (hA0 : A0 ≠ 0)
    (R1 : B0 ^ 2 = A0 ^ 2 + A2 ^ 2) (R2 : B1 ^ 2 = A0 ^ 2 - A2 ^ 2) (R3 : B2 ^ 2 = 2 * A0 * A2)
    (rJ : A0 ^ 4 = A1 ^ 4 + A2 ^ 4) (R5 : A0 * B0 = A2 * B1 + A1 * B2)
    (hne : A2 ^ 4 - 2 * A0 ^ 2 * A2 ^ 2 - A0 ^ 4 ≠ 0) :
    CM24Alg.mpoly (A2 ^ 2 / A0 ^ 2) = 0 := by
  set Q := A0 ^ 4 + A2 ^ 4 - 2 * A0 * A1 ^ 2 * A2
  have E1 : 2 * A1 * A2 * B1 * B2 = Q := by
    linear_combination (-(A0 * B0 + A2 * B1 + A1 * B2)) * R5 + A0 ^ 2 * R1 - A2 ^ 2 * R2 - A1 ^ 2 * R3
  have E2 : 8 * A0 * A1 ^ 2 * A2 ^ 3 * (A0 ^ 2 - A2 ^ 2) = Q ^ 2 := by
    linear_combination (2 * A1 * A2 * B1 * B2 + Q) * E1 - 4 * A1 ^ 2 * A2 ^ 2 * B2 ^ 2 * R2
      - 4 * A1 ^ 2 * A2 ^ 2 * (A0 ^ 2 - A2 ^ 2) * R3
  set W := A0 ^ 4 + 2 * A0 ^ 2 * A2 ^ 2 - A2 ^ 4
  set V := (A0 ^ 4 + A2 ^ 4) ^ 2 + 4 * A0 ^ 2 * A2 ^ 2 * (A0 ^ 4 - A2 ^ 4)
  have E3 : 4 * A0 * A2 * A1 ^ 2 * W = V := by
    linear_combination E2 - 4 * A0 ^ 2 * A2 ^ 2 * rJ
  have E4 : 16 * A0 ^ 2 * A2 ^ 2 * (A0 ^ 4 - A2 ^ 4) * W ^ 2 = V ^ 2 := by
    linear_combination (4 * A0 * A2 * A1 ^ 2 * W + V) * E3 + 16 * A0 ^ 2 * A2 ^ 2 * W ^ 2 * rJ
  have E5 : (A2 ^ 4 - 2 * A0 ^ 2 * A2 ^ 2 - A0 ^ 4) ^ 2 * (A2 ^ 8 + 12 * A2 ^ 6 * A0 ^ 2 + 2 * A2 ^ 4 * A0 ^ 4
      - 12 * A2 ^ 2 * A0 ^ 6 + A0 ^ 8) = 0 := by
    linear_combination -E4
  have hmh := (mul_eq_zero.1 E5).resolve_left (pow_ne_zero _ hne)
  unfold CM24Alg.mpoly
  field_simp
  linear_combination hmh

/-- **`mpoly(θ₁₀(i√6)²/θ₀₀(i√6)²) = 0`, proved (no leaf).** -/
theorem mpoly_theta : th1 τ6 0 0 ≠ 0 ∧ CM24Alg.mpoly (th1 τ6 (1 / 2) 0 ^ 2 / th1 τ6 0 0 ^ 2) = 0 := by
  set A0 := th1 τ6 0 0
  set A1 := th1 τ6 0 (1 / 2)
  set A2 := th1 τ6 (1 / 2) 0
  set B0 := th1 τ3 0 0
  set B1 := th1 τ3 0 (1 / 2)
  set B2 := th1 τ3 (1 / 2) 0
  set K := 1 / (-I * τ3) ^ (1 / 2 : ℂ)
  -- real positive values on the imaginary axis
  set a0 := ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 0) ^ 2)
  set a2 := ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 1 / 2) ^ 2)
  set p1 := ∑' n : ℤ, Real.exp (-π * (r6 / 3) * ((n : ℝ) + 1 / 2) ^ 2)
  set kr := 1 / (r6 / 2) ^ (1 / 2 : ℝ)
  have ha0 : 0 < a0 := th1_imag_pos r6_pos 0
  have hp1 : 0 < p1 := th1_imag_pos (div_pos r6_pos (by norm_num)) _
  have hA0 : A0 = (a0 : ℂ) := by simp only [A0, a0]; rw [τ6_eq', th1_imag]
  have hA2 : A2 = (a2 : ℂ) := by simp only [A2, a2]; rw [τ6_eq', th1_imag]
  have hA0ne : A0 ≠ 0 := by rw [hA0]; exact_mod_cast ha0.ne'
  -- `S`: the theta constants at `τ₃` from those at `τ' = −1/τ₃`
  have hB0 : B0 = K * th1 τp 0 0 := by simp only [B0, K]; rw [sA, τp_eq]
  have hB1 : B1 = K * th1 τp (1 / 2) 0 := by simp only [B1, K]; rw [sB τ3_ne, τp_eq]
  have hB2 : B2 = K * th1 τp 0 (1 / 2) := by simp only [B2, K]; rw [sC τ3_ne, τp_eq]
  have hB1r : B1 = ((kr * p1 : ℝ) : ℂ) := by
    rw [hB1, show K = (kr : ℂ) from K_real, τp, th1_imag, Complex.ofReal_mul]
  -- Landen at `τ₃` and Jacobi at `τ₆`
  have R1 : B0 ^ 2 = A0 ^ 2 + A2 ^ 2 := by have := dupA τ3_im; rw [h2τ3] at this; exact this
  have R2 : B1 ^ 2 = A0 ^ 2 - A2 ^ 2 := by have := dupB τ3_im; rw [h2τ3] at this; exact this
  have R3 : B2 ^ 2 = 2 * A0 * A2 := by have := dupC τ3_im; rw [h2τ3] at this; exact this
  have rJ : A0 ^ 4 = A1 ^ 4 + A2 ^ 4 := jacobi τ6_im
  -- the cubic modular equation at `τ'` (`3τ' = τ₆`)
  have hc := cubic τp_im
  rw [h3τp] at hc
  have R5 : A0 * B0 = A2 * B1 + A1 * B2 := by
    rw [hB0, hB1, hB2]; linear_combination K * hc
  -- `0 < θ₁₀(i√6)² < θ₀₀(i√6)²` excludes the spurious factor
  have hlt : a2 ^ 2 < a0 ^ 2 := by
    have h := R2
    rw [hB1r, hA0, hA2] at h
    have h' : (kr * p1) ^ 2 = a0 ^ 2 - a2 ^ 2 := by exact_mod_cast h
    have : 0 < (kr * p1) ^ 2 := by have := K_pos; positivity
    linarith
  have hne : A2 ^ 4 - 2 * A0 ^ 2 * A2 ^ 2 - A0 ^ 4 ≠ 0 := by
    rw [hA0, hA2]
    have : a2 ^ 4 - 2 * a0 ^ 2 * a2 ^ 2 - a0 ^ 4 < 0 := by nlinarith [sq_nonneg a2, sq_nonneg a0]
    exact_mod_cast this.ne
  exact ⟨hA0ne, mpoly_A A0 A1 A2 B0 B1 B2 hA0ne R1 R2 R3 rJ R5 hne⟩

/-- **`ThetaValueAtOmega24`, proved (no leaf).** -/
theorem thetaValueAtOmega24 : ThetaValueAtOmega24 :=
  thetaValueAtOmega24_of_mpoly _ mpoly_theta.1
    (div_mul_cancel₀ (th1 τ6 (1 / 2) 0 ^ 2) (pow_ne_zero 2 mpoly_theta.1)).symm mpoly_theta.2

/-! ## Bonus: the classical singular modulus `λ*(6) = (2−√3)(√3−√2)`, proved -/

theorem a0_ge_one : 1 ≤ ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 0) ^ 2) := by
  have := (summable_gauss r6_pos 0).le_tsum 0 (fun j _ => (Real.exp_pos _).le)
  simpa using this

theorem a2_le : ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 1 / 2) ^ 2) ≤
    2 * (Real.exp (-(π * r6) / 4) * (1 - Real.exp (-(π * r6)))⁻¹) := by
  set c := π * r6 with hcdef
  have hc : 0 < c := mul_pos Real.pi_pos r6_pos
  have hs := summable_gauss r6_pos (1 / 2)
  have hinj : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro x y h; simp only [neg_inj, add_left_inj, Nat.cast_inj] at h; exact h
  have h1 : Summable (fun n : ℕ => Real.exp (-π * r6 * (((n : ℤ) : ℝ) + 1 / 2) ^ 2)) :=
    hs.comp_injective Nat.cast_injective
  have h2 : Summable (fun n : ℕ => Real.exp (-π * r6 * (((-((n : ℤ) + 1) : ℤ) : ℝ) + 1 / 2) ^ 2)) :=
    hs.comp_injective hinj
  rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ => Real.exp (-π * r6 * ((n : ℝ) + 1 / 2) ^ 2)) h1 h2]
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hg : Summable (fun n : ℕ => Real.exp (-c / 4) * Real.exp (-c) ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hgs : ∑' n : ℕ, Real.exp (-c / 4) * Real.exp (-c) ^ n = Real.exp (-c / 4) * (1 - Real.exp (-c))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have b1 : ∀ n : ℕ, Real.exp (-π * r6 * (((n : ℤ) : ℝ) + 1 / 2) ^ 2) ≤ Real.exp (-c / 4) * Real.exp (-c) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg
    push_cast
    nlinarith [mul_nonneg hc.le (sq_nonneg (n : ℝ))]
  have b2 : ∀ n : ℕ, Real.exp (-π * r6 * (((-((n : ℤ) + 1) : ℤ) : ℝ) + 1 / 2) ^ 2) ≤
      Real.exp (-c / 4) * Real.exp (-c) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg
    push_cast
    nlinarith [mul_nonneg hc.le (sq_nonneg (n : ℝ))]
  have t1 := h1.tsum_le_tsum b1 hg
  have t2 := h2.tsum_le_tsum b2 hg
  rw [hgs] at t1 t2
  linarith

theorem a2_lt : ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 1 / 2) ^ 2) < 7 / 10 := by
  refine lt_of_le_of_lt a2_le ?_
  have hpi := Real.pi_gt_three
  have hr6 : 12 / 5 < r6 := by nlinarith [r6_sq, r6_pos]
  have hc : 36 / 5 < π * r6 := by nlinarith
  have e8 : 1 + π * r6 / 8 ≤ Real.exp (π * r6 / 8) := by linarith [Real.add_one_le_exp (π * r6 / 8)]
  have e4 : Real.exp (π * r6 / 4) = Real.exp (π * r6 / 8) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e1 : 1 + π * r6 ≤ Real.exp (π * r6) := by linarith [Real.add_one_le_exp (π * r6)]
  have q1 : Real.exp (-(π * r6) / 4) = (Real.exp (π * r6 / 4))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  have q2 : Real.exp (-(π * r6)) = (Real.exp (π * r6))⁻¹ := by rw [← Real.exp_neg]
  have hE4 : 361 / 100 ≤ Real.exp (π * r6 / 4) := by rw [e4]; nlinarith
  have hE1 : 41 / 5 ≤ Real.exp (π * r6) := by linarith
  rw [q1, q2]
  have p4 : 0 < Real.exp (π * r6 / 4) := Real.exp_pos _
  have p1 : 0 < Real.exp (π * r6) := Real.exp_pos _
  have i4 : (Real.exp (π * r6 / 4))⁻¹ ≤ 100 / 361 := by
    rw [inv_le_comm₀ p4 (by norm_num)]; linarith
  have i1 : (Real.exp (π * r6))⁻¹ ≤ 5 / 41 := by
    rw [inv_le_comm₀ p1 (by norm_num)]; linarith
  have i1' : 36 / 41 ≤ 1 - (Real.exp (π * r6))⁻¹ := by linarith
  have i2 : (1 - (Real.exp (π * r6))⁻¹)⁻¹ ≤ 41 / 36 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have : 0 ≤ (Real.exp (π * r6 / 4))⁻¹ := inv_nonneg.2 p4.le
  have : 0 ≤ (1 - (Real.exp (π * r6))⁻¹)⁻¹ := inv_nonneg.2 (by linarith)
  nlinarith

/-- The four roots of `mpoly`: only `(2−√3)(√3−√2)` lies in `(0, 1/2)`. -/
theorem root_select (k : ℝ) (hm : k ^ 4 + 12 * k ^ 3 + 2 * k ^ 2 - 12 * k + 1 = 0) (h0 : 0 < k) (h1 : k < 1 / 2) :
    k = (2 - √3) * (√3 - √2) := by
  set a := √2 with ha'
  set b := √3 with hb'
  have ha : a ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hb : b ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have a0 : 0 < a := Real.sqrt_pos.2 (by norm_num)
  have b0 : 0 < b := Real.sqrt_pos.2 (by norm_num)
  have hfac : (k - (2 - b) * (b - a)) * (k + (2 + b) * (b - a)) * (k - (2 - b) * (b + a)) * (k + (2 + b) * (b + a)) =
      k ^ 4 + 12 * k ^ 3 + 2 * k ^ 2 - 12 * k + 1 := by
    linear_combination (a^2*b^4 - 8*a^2*b^2 + 16*a^2 - 2*b^6 + b^4*(18 - 4*k) + b^2*(-2*k^2 + 16*k - 48) - 8*k^2 + 32) * ha + (b^6 + b^4*(4*k - 9) + b^2*(6*k^2 - 12*k + 25) + 4*k^3 + 6*k^2 - 4*k - 21) * hb
  rw [hm] at hfac
  have hba : a < b := by nlinarith
  have hb2 : b < 7 / 4 := by nlinarith
  have hab : 3 < a + b := by nlinarith
  have f2 : 0 < k + (2 + b) * (b - a) := by nlinarith
  have f3 : k - (2 - b) * (b + a) < 0 := by nlinarith
  have f4 : 0 < k + (2 + b) * (b + a) := by nlinarith
  have hne : (k + (2 + b) * (b - a)) * (k - (2 - b) * (b + a)) * (k + (2 + b) * (b + a)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero f2.ne' f3.ne) f4.ne'
  have : (k - (2 - b) * (b - a)) * ((k + (2 + b) * (b - a)) * (k - (2 - b) * (b + a)) * (k + (2 + b) * (b + a))) = 0 := by
    linear_combination hfac
  have := (mul_eq_zero.1 this).resolve_right hne
  linarith

/-- **The singular modulus `k₆`, proved**: the leaf variant `SingularModulus6` is a theorem. -/
theorem singularModulus6 : SingularModulus6 := by
  obtain ⟨hA0ne, hm⟩ := mpoly_theta
  set a0 := ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 0) ^ 2)
  set a2 := ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 1 / 2) ^ 2)
  have hA0 : th1 τ6 0 0 = (a0 : ℂ) := by rw [τ6_eq', th1_imag]
  have hA2 : th1 τ6 (1 / 2) 0 = (a2 : ℂ) := by rw [τ6_eq', th1_imag]
  have ha0 : 1 ≤ a0 := a0_ge_one
  have ha2 : 0 < a2 := th1_imag_pos r6_pos _
  have ha2' : a2 < 7 / 10 := a2_lt
  rw [hA0, hA2] at hm
  have hmr : (a2 ^ 2 / a0 ^ 2) ^ 4 + 12 * (a2 ^ 2 / a0 ^ 2) ^ 3 + 2 * (a2 ^ 2 / a0 ^ 2) ^ 2
      - 12 * (a2 ^ 2 / a0 ^ 2) + 1 = 0 := by
    unfold CM24Alg.mpoly at hm; exact_mod_cast hm
  have hk0 : 0 < a2 ^ 2 / a0 ^ 2 := by positivity
  have hk1 : a2 ^ 2 / a0 ^ 2 < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hk := root_select _ hmr hk0 hk1
  refine ⟨by rw [← A0_eq, hA0]; exact_mod_cast (by linarith : (0 : ℝ) < a0).ne', ?_⟩
  rw [← A0_eq, ← A2_eq, hA0, hA2, ← hk]
  have : (a0 : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < a0).ne'
  push_cast
  field_simp

/-- **The field `igusaCMValue24`, proved.** -/
theorem igusaCMValue24 : IgusaCMValue24 :=
  igusa_of_thetaQuotientValue24 (thetaQuotientValue24_iff.2 thetaValueAtOmega24)

/-- **The glue `ThetaQuotientValue24`, proved.** -/
theorem thetaQuotientValue24 : HDec.LeafQCheck.HM.QMSplit.ThetaQuotientValue24 :=
  thetaQuotientValue24_iff.2 thetaValueAtOmega24

/-- **The field `igusaCMValue24` from the singular modulus `k₆`.** -/
theorem igusaCMValue24_of_singularModulus6 (h : SingularModulus6) : IgusaCMValue24 :=
  igusa_of_thetaQuotientValue24 (thetaQuotientValue24_iff.2 (thetaValueAtOmega24_of_singularModulus6 h))

/-- The glue `ThetaQuotientValue24` from the singular modulus `k₆`. -/
theorem thetaQuotientValue24_of_singularModulus6 (h : SingularModulus6) :
    HDec.LeafQCheck.HM.QMSplit.ThetaQuotientValue24 :=
  thetaQuotientValue24_iff.2 (thetaValueAtOmega24_of_singularModulus6 h)

end CM24

/-- The field `igusaCMValue24`, at its fully qualified type. -/
theorem CM24.igusaCMValue24_field : HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24 := CM24.igusaCMValue24
/-- The glue `ThetaQuotientValue24`, at its fully qualified type. -/
theorem CM24.thetaQuotientValue24_field : HDec.LeafQCheck.HM.QMSplit.ThetaQuotientValue24 :=
  CM24.thetaQuotientValue24
/-- The closed numeric statement, at its fully qualified type. -/
theorem CM24.thetaValueAtOmega24_field : HDec.LeafQCheck.HM.QMSplit.Value24.ThetaValueAtOmega24 :=
  CM24.thetaValueAtOmega24

#print axioms CM24.igusaCMValue24_field
#print axioms CM24.singularModulus6
#print axioms CM24.thetaQuotientValue24_field
#print axioms CM24.thetaValueAtOmega24_of_singularModulus6
#print axioms CM24.igusaCMValue24_of_singularModulus6
#print axioms CM24.thetaValueAtOmega24
#print axioms CM24.igusaCMValue24
#print axioms CM24.thetaQuotientValue24

end

namespace HDec

namespace HSyn

/-- **The added leaves still open** (leaf-fold12): route-a-fold's `OpenAddedLeaves10` without
`igusaCMValue24`, which cm24-value proves (`CM24.igusaCMValue24_field`). 13 fields. -/
structure OpenAddedLeaves11 : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  x6ConicModel : X6Kummer.X6ConicModel
  shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  shimuraGoodReductionNoGuard : CurveSplitGR.ShimuraGoodReductionNoGuard
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop. 2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- qm-split, H-87/H-88: `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` (Shimura 1971 Prop. 9.2;
  Shimizu 1965). -/
  shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1
  /-- shimura-glue, printed form, on abelian schemes (route-a-fold): Deligne's theorem on the connected
  components of a Shimura variety for `G = B^×` at level `K₃` on one fine witness `Y₃` (Deligne, Sém. Bourbaki
  389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.1.3, 2.6.3; locators UNVERIFIED). -/
  deligneComponentsY3PrintedAb : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb

/-- route-a-fold's added-leaf bundle from leaf-fold12's: `igusaCMValue24` is cm24-value's theorem. -/
theorem addedLeaves10_of_open11 (l : OpenAddedLeaves11) : OpenAddedLeaves10 where
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  shimuraTaniyamaQbar := l.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  shimuraGoodReductionNoGuard := l.shimuraGoodReductionNoGuard
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
  igusaCMValue24 := _root_.CM24.igusaCMValue24_field
  deligneComponentsY3PrintedAb := l.deligneComponentsY3PrintedAb

/-- **G0 with only the open leaves and the open glue** (leaf-fold12; no `sorry`, standard axioms).
`ZInQ.SixContactMin` from `OpenResearchLeaves11` (29), `OpenTextbookLeaves10` (15), `OpenAddedLeaves11` (13) and
`OpenGlue7` (1). -/
theorem sixContactMin_of_open14 (r : OpenResearchLeaves11) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves11)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) : ZInQ.SixContactMin :=
  sixContactMin_of_open13 r t (addedLeaves10_of_open11 l) g hYu hθ

end HSyn

end HDec

#print axioms HDec.HSyn.addedLeaves10_of_open11
#print axioms HDec.HSyn.sixContactMin_of_open14
