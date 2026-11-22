import ZInQKernel.Contrib.OneProof.ThetaDirect.Kron
import ZInQKernel.Contrib.OneProof.ThetaDirect.Split

/-! theta-direct: copied verbatim from origin/wip/theta-fold (8e3dbdea) `ZInQKernel/Contrib/OneProof/LinYangGlue.lean`;
   only the import lines are changed (this base has no theta-fold modules). -/

/-! # theta-fold (3/4): theta-glue's Igusa theta expressions and igusa-alg's `ThetaRatiosAtQM` from
`LinYangThetaCurve`

theta-glue's scratch/theta-glue/ThetaGlue.lean (the duplication formula, `ThetaEightSquare`, Igusa's theta
expressions `psi4Th`, `psi6Th`, `chi10Th`, `chi12Th`, theta-glue's composite `LinYangThetaCurve`, the reduction to
`IgusaAlg k`) with igusa-alg's Kronecker proofs of `IgusaAlg 3..9`, and igusa-alg's final theorems
(`thetaRatiosAtQM_of_linYang`, `thetaPointOfFibre_of_linYang`); verbatim through linyang-printed's
LinYangPrintedFull.lean. docs/research/theta-fold.md. -/

noncomputable section

namespace HDec.HSyn.G0Split.ThetaPt.ThetaGlue

open Complex Matrix
open _root_.ZInQ.LeafPush2 (IsSiegel)
open Polynomial (C X aeval)

/-! ## 0. theta-split's statements

theta-glue copied `thetaEight`, `qmR`, `ThetaEightSquare` and `QMThetaSymmetricCurve` verbatim from theta-split;
theta-fold uses theta-split's declarations (`LinYangSplit`) instead, under the same names. -/

export ThetaSplit (thetaEight qmR ThetaEightSquare QMThetaSymmetricCurve esymm_cons_succ)

/-! ## 1. Absolute convergence and the duplication formula -/

/-- The summand of `PkgI1.thetaConst m Ω` (verbatim body). -/
def thetaTerm (m : PkgI1.Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (n : Fin 2 → ℤ) : ℂ :=
  let v : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2
  Complex.exp (Real.pi * I * (v ⬝ᵥ (Ω *ᵥ v)) + Real.pi * I * (v ⬝ᵥ fun k => ((m.2 k : ℕ) : ℂ)))

theorem thetaConst_eq_tsum (m : PkgI1.Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    PkgI1.thetaConst m Ω = ∑' n, thetaTerm m Ω n := rfl

/-- The real point `x = n + a/2`. -/
def xr (m : PkgI1.Char2) (n : Fin 2 → ℤ) (k : Fin 2) : ℝ := (n k : ℝ) + ((m.1 k : ℕ) : ℝ) / 2

theorem thetaTerm_coord (m : PkgI1.Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (n : Fin 2 → ℤ) :
    thetaTerm m Ω n = Complex.exp (Real.pi * I *
      ((xr m n 0 : ℂ) * (Ω 0 0 * xr m n 0 + Ω 0 1 * xr m n 1) +
        (xr m n 1 : ℂ) * (Ω 1 0 * xr m n 0 + Ω 1 1 * xr m n 1)) +
      Real.pi * I * ((xr m n 0 : ℂ) * ((m.2 0 : ℕ) : ℂ) + (xr m n 1 : ℂ) * ((m.2 1 : ℕ) : ℂ))) := by
  simp only [thetaTerm, xr, dotProduct, mulVec, Fin.sum_univ_two]
  push_cast
  ring_nf

/-- The quadratic form of `Im Ω` at a real point. -/
def qY (Ω : Matrix (Fin 2) (Fin 2) ℂ) (x0 x1 : ℝ) : ℝ :=
  x0 * ((Ω 0 0).im * x0 + (Ω 0 1).im * x1) + x1 * ((Ω 1 0).im * x0 + (Ω 1 1).im * x1)

theorem norm_thetaTerm (m : PkgI1.Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (n : Fin 2 → ℤ) :
    ‖thetaTerm m Ω n‖ = Real.exp (-Real.pi * qY Ω (xr m n 0) (xr m n 1)) := by
  rw [thetaTerm_coord, Complex.norm_exp]
  congr 1
  simp only [qY, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im]
  ring

/-- Positive-definiteness bound: `(y₀₀+y₁₁)·q_Y(x) ≥ det(Y)·|x|²` (sum of two squares). -/
theorem qY_lower (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hs : (Ω 0 1).im = (Ω 1 0).im) (x0 x1 : ℝ) :
    ((Ω 0 0).im * (Ω 1 1).im - (Ω 0 1).im ^ 2) * (x0 ^ 2 + x1 ^ 2) ≤
      ((Ω 0 0).im + (Ω 1 1).im) * qY Ω x0 x1 := by
  have h : ((Ω 0 0).im + (Ω 1 1).im) * qY Ω x0 x1 -
      ((Ω 0 0).im * (Ω 1 1).im - (Ω 0 1).im ^ 2) * (x0 ^ 2 + x1 ^ 2) =
      ((Ω 0 0).im * x0 + (Ω 0 1).im * x1) ^ 2 + ((Ω 0 1).im * x0 + (Ω 1 1).im * x1) ^ 2 := by
    simp only [qY]; rw [← hs]; ring
  nlinarith [sq_nonneg ((Ω 0 0).im * x0 + (Ω 0 1).im * x1),
    sq_nonneg ((Ω 0 1).im * x0 + (Ω 1 1).im * x1)]

/-- From `IsSiegel`: a uniform positive lower bound for `q_Y`. -/
theorem exists_qY_lower {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    ∃ ε > 0, ∀ x0 x1 : ℝ, ε * (x0 ^ 2 + x1 ^ 2) ≤ qY Ω x0 x1 := by
  obtain ⟨hT, hP⟩ := hΩ
  have hs : (Ω 0 1).im = (Ω 1 0).im := by
    have := congrFun (congrFun hT 1) 0
    simp only [Matrix.transpose_apply] at this
    rw [this]
  have hdet := hP.det_pos
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.map_apply] at hdet
  have h00 : 0 < (Ω 0 0).im := by
    simpa using hP.diag_pos (i := 0)
  have h11 : 0 < (Ω 1 1).im := by
    simpa using hP.diag_pos (i := 1)
  refine ⟨((Ω 0 0).im * (Ω 1 1).im - (Ω 0 1).im ^ 2) / ((Ω 0 0).im + (Ω 1 1).im), ?_, ?_⟩
  · apply div_pos _ (by linarith)
    rw [← hs] at hdet; nlinarith
  · intro x0 x1
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith), mul_comm _ ((Ω 0 0).im + (Ω 1 1).im)]
    exact qY_lower Ω hs x0 x1


theorem sq_xr_ge (m : PkgI1.Char2) (n : Fin 2 → ℤ) (k : Fin 2) :
    (n k : ℝ) ^ 2 - |(n k : ℝ)| ≤ xr m n k ^ 2 := by
  have ha0 : (0 : ℝ) ≤ ((m.1 k : ℕ) : ℝ) := by positivity
  have ha1 : ((m.1 k : ℕ) : ℝ) ≤ 1 := by
    have := (m.1 k).isLt; exact_mod_cast Nat.lt_succ_iff.mp this
  simp only [xr]
  have h1 : -|(n k : ℝ)| ≤ (n k : ℝ) := neg_abs_le _
  have h2 : 0 ≤ |(n k : ℝ)| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left (le_abs_self (-(n k : ℝ))) ha0,
    mul_le_mul_of_nonneg_right ha1 h2, sq_nonneg (((m.1 k : ℕ) : ℝ))]

/-- The Gaussian majorant `n ↦ exp(-π(εn² - ε|n|))` (Mathlib's `jacobiTheta₂` bound). -/
def gMaj (ε : ℝ) (n : ℤ) : ℝ := Real.exp (-Real.pi * (ε * (n : ℝ) ^ 2 - 2 * (ε / 2) * |(n : ℝ)|))

theorem summable_gMaj {ε : ℝ} (hε : 0 < ε) : Summable (gMaj ε) := by
  have := summable_pow_mul_jacobiTheta₂_term_bound (ε / 2) hε 0
  simp only [pow_zero, one_mul] at this
  exact this.congr fun n => by simp [gMaj, Int.cast_abs]

theorem norm_thetaTerm_le {Ω : Matrix (Fin 2) (Fin 2) ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x0 x1 : ℝ, ε * (x0 ^ 2 + x1 ^ 2) ≤ qY Ω x0 x1) (m : PkgI1.Char2) (n : Fin 2 → ℤ) :
    ‖thetaTerm m Ω n‖ ≤ gMaj ε (n 0) * gMaj ε (n 1) := by
  rw [norm_thetaTerm, gMaj, gMaj, ← Real.exp_add, Real.exp_le_exp]
  have h0 := sq_xr_ge m n 0
  have h1 := sq_xr_ge m n 1
  have hq := h (xr m n 0) (xr m n 1)
  have hpi := Real.pi_pos
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h0 h1) hε.le]

theorem summable_norm_thetaTerm {Ω : Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∃ ε > 0, ∀ x0 x1 : ℝ, ε * (x0 ^ 2 + x1 ^ 2) ≤ qY Ω x0 x1) (m : PkgI1.Char2) :
    Summable (fun n => ‖thetaTerm m Ω n‖) := by
  obtain ⟨ε, hε, h⟩ := h
  have hg := summable_gMaj hε
  have hpos : 0 ≤ gMaj ε := fun n => (Real.exp_pos _).le
  have hp : Summable (fun p : ℤ × ℤ => gMaj ε p.1 * gMaj ε p.2) := hg.mul_of_nonneg hg hpos hpos
  have hp' : Summable (fun n : Fin 2 → ℤ => gMaj ε (n 0) * gMaj ε (n 1)) :=
    (finTwoArrowEquiv ℤ).summable_iff.mpr hp
  exact hp'.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_thetaTerm_le hε h m)

theorem qY_two_smul (Ω : Matrix (Fin 2) (Fin 2) ℂ) (x0 x1 : ℝ) :
    qY ((2 : ℂ) • Ω) x0 x1 = 2 * qY Ω x0 x1 := by
  simp only [qY, Matrix.smul_apply, smul_eq_mul, Complex.mul_im]
  norm_num
  ring

theorem exists_qY_lower_two {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    ∃ ε > 0, ∀ x0 x1 : ℝ, ε * (x0 ^ 2 + x1 ^ 2) ≤ qY ((2 : ℂ) • Ω) x0 x1 := by
  obtain ⟨ε, hε, h⟩ := exists_qY_lower hΩ
  refine ⟨2 * ε, by positivity, fun x0 x1 => ?_⟩
  rw [qY_two_smul]; nlinarith [h x0 x1]


/-! ## 2. The duplication formula -/

theorem fin2_add_castC (x y : Fin 2) :
    (((x + y : Fin 2) : ℕ) : ℂ) = ((x : ℕ) : ℂ) + ((y : ℕ) : ℂ) - 2 * ((x : ℕ) : ℂ) * ((y : ℕ) : ℂ) := by
  fin_cases x <;> fin_cases y <;> norm_num

/-- The change of variables `(c, k, l) ↦ (n₁, n₂)`, `n₁ = l + k + c(1-a)`, `n₂ = l - k - ca`
(so `n₁ + a/2 = q + p`, `n₂ + a/2 = q - p` with `p = k + c/2`, `q = l + (c⊕a)/2`). -/
def dupMap (a : Fin 2 → Fin 2) (x : (Fin 2 → Fin 2) × ((Fin 2 → ℤ) × (Fin 2 → ℤ))) :
    (Fin 2 → ℤ) × (Fin 2 → ℤ) :=
  (fun i => x.2.2 i + x.2.1 i + ((x.1 i : ℕ) : ℤ) * (1 - ((a i : ℕ) : ℤ)),
   fun i => x.2.2 i - x.2.1 i - ((x.1 i : ℕ) : ℤ) * ((a i : ℕ) : ℤ))

/-- Parity of an integer as an element of `Fin 2`. -/
def par (z : ℤ) : Fin 2 := if z % 2 = 0 then 0 else 1

theorem fin2_cases (x : Fin 2) : ((x : ℕ) : ℤ) = 0 ∨ ((x : ℕ) : ℤ) = 1 := by
  fin_cases x <;> simp

theorem par_two_mul_add (K : ℤ) (c : Fin 2) : par (2 * K + ((c : ℕ) : ℤ)) = c := by
  fin_cases c
  · simp [par]
  · simp only [par]
    split_ifs with h
    · simp at h
    · rfl

theorem par_cast (z : ℤ) : (((par z : Fin 2) : ℕ) : ℤ) = z % 2 := by
  unfold par; split_ifs with h
  · simp [h]
  · simp; omega

/-- Its inverse. -/
def dupInv (a : Fin 2 → Fin 2) (y : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    (Fin 2 → Fin 2) × ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  (fun i => par (y.1 i - y.2 i), fun i => (y.1 i - y.2 i) / 2,
    fun i => y.1 i - (y.1 i - y.2 i) / 2 - ((par (y.1 i - y.2 i) : ℕ) : ℤ) * (1 - ((a i : ℕ) : ℤ)))

def dupEquiv (a : Fin 2 → Fin 2) :
    (Fin 2 → Fin 2) × ((Fin 2 → ℤ) × (Fin 2 → ℤ)) ≃ (Fin 2 → ℤ) × (Fin 2 → ℤ) where
  toFun := dupMap a
  invFun := dupInv a
  left_inv := by
    rintro ⟨c, k, l⟩
    have hd : ∀ i, (dupMap a (c, k, l)).1 i - (dupMap a (c, k, l)).2 i =
        2 * k i + ((c i : ℕ) : ℤ) := by
      intro i; simp only [dupMap]; ring
    have hk : ∀ i, (2 * k i + ((c i : ℕ) : ℤ)) / 2 = k i := by
      intro i; rcases fin2_cases (c i) with h | h <;> rw [h] <;> omega
    simp only [dupInv, hd, par_two_mul_add, hk, Prod.mk.injEq]
    refine ⟨trivial, trivial, funext fun i => ?_⟩
    simp only [dupMap]; ring
  right_inv := by
    rintro ⟨n1, n2⟩
    simp only [dupInv, dupMap, Prod.mk.injEq, par_cast]
    constructor
    · funext i; ring
    · funext i
      rcases fin2_cases (a i) with h' | h' <;> rw [h'] <;> omega

/-- The sign `exp(πi (c⊕a)·b)`. -/
def dupSign (a b c : Fin 2 → Fin 2) : ℂ :=
  Complex.exp (Real.pi * I * (((((c + a) 0 : Fin 2) : ℕ) : ℂ) * ((b 0 : ℕ) : ℂ) +
    ((((c + a) 1 : Fin 2) : ℕ) : ℂ) * ((b 1 : ℕ) : ℂ)))

theorem thetaTerm_mul_dupMap (Ω : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2 → Fin 2)
    (x : (Fin 2 → Fin 2) × ((Fin 2 → ℤ) × (Fin 2 → ℤ))) :
    thetaTerm (a, b) Ω (dupMap a x).1 * thetaTerm (a, b) Ω (dupMap a x).2 =
      dupSign a b x.1 * (thetaTerm (x.1, 0) ((2 : ℂ) • Ω) x.2.1 *
        thetaTerm (x.1 + a, 0) ((2 : ℂ) • Ω) x.2.2) := by
  obtain ⟨c, k, l⟩ := x
  simp only [thetaTerm_coord, dupSign, xr, dupMap, Pi.add_apply, Pi.zero_apply, Fin.val_zero,
    Matrix.smul_apply, smul_eq_mul]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨l 0 * ((b 0 : ℕ) : ℤ) + l 1 * ((b 1 : ℕ) : ℤ), ?_⟩
  push_cast
  rw [fin2_add_castC, fin2_add_castC]
  ring


/-- **Duplication formula (proved).** For `Ω ∈ 𝔥₂` and any characteristic `(a, b)`:
`θ[a;b](Ω)² = Σ_c exp(πi (c⊕a)·b) θ[c;0](2Ω) θ[c⊕a;0](2Ω)`. -/
theorem thetaConst_sq_eq {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω)
    (a b : Fin 2 → Fin 2) :
    PkgI1.thetaConst (a, b) Ω ^ 2 = ∑ c : Fin 2 → Fin 2, dupSign a b c *
      (PkgI1.thetaConst (c, 0) ((2 : ℂ) • Ω) * PkgI1.thetaConst (c + a, 0) ((2 : ℂ) • Ω)) := by
  have h1 := summable_norm_thetaTerm (exists_qY_lower hΩ)
  have h2 := summable_norm_thetaTerm (exists_qY_lower_two hΩ)
  simp only [thetaConst_eq_tsum]
  rw [sq, tsum_mul_tsum_of_summable_norm (h1 (a, b)) (h1 (a, b))]
  have hF : Summable (fun p : (Fin 2 → ℤ) × (Fin 2 → ℤ) =>
      thetaTerm (a, b) Ω p.1 * thetaTerm (a, b) Ω p.2) :=
    (summable_mul_of_summable_norm (h1 (a, b)) (h1 (a, b)))
  rw [← (dupEquiv a).tsum_eq]
  have hG : Summable (fun x => thetaTerm (a, b) Ω (dupEquiv a x).1 *
      thetaTerm (a, b) Ω (dupEquiv a x).2) := (dupEquiv a).summable_iff.mpr hF
  rw [hG.tsum_prod, tsum_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc : ∀ y : (Fin 2 → ℤ) × (Fin 2 → ℤ), thetaTerm (a, b) Ω (dupEquiv a (c, y)).1 *
      thetaTerm (a, b) Ω (dupEquiv a (c, y)).2 = dupSign a b c *
        (thetaTerm (c, 0) ((2 : ℂ) • Ω) y.1 * thetaTerm (c + a, 0) ((2 : ℂ) • Ω) y.2) :=
    fun y => thetaTerm_mul_dupMap Ω a b (c, y)
  simp only [hc]
  rw [tsum_mul_left, tsum_mul_tsum_of_summable_norm (h2 (c, 0)) (h2 (c + a, 0))]


/-! ## The ten explicit squares -/

theorem univ_fin2_fin2 : (Finset.univ : Finset (Fin 2 → Fin 2)) =
    {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by decide

theorem dupSign_eq (a b c : Fin 2 → Fin 2) : dupSign a b c =
    (-1) ^ ((((c + a) 0 : Fin 2) : ℕ) * (b 0 : ℕ) + (((c + a) 1 : Fin 2) : ℕ) * (b 1 : ℕ)) := by
  rw [dupSign, ← Complex.exp_pi_mul_I, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

/-- `U c = θ[c;0](2Ω)`, indexed `U₀ = U_{00}, U₁ = U_{01}, U₂ = U_{10}, U₃ = U_{11}`. -/
def U2 (Ω : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 4) : ℂ :=
  PkgI1.thetaConst (![![0, 0], ![0, 1], ![1, 0], ![1, 1]] i, 0) ((2 : ℂ) • Ω)

theorem sq_expand {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω)
    (a b : Fin 2 → Fin 2) :
    PkgI1.thetaConst (a, b) Ω ^ 2 =
      dupSign a b ![0, 0] * (U2 Ω 0 * PkgI1.thetaConst (![0, 0] + a, 0) ((2 : ℂ) • Ω)) +
      dupSign a b ![0, 1] * (U2 Ω 1 * PkgI1.thetaConst (![0, 1] + a, 0) ((2 : ℂ) • Ω)) +
      dupSign a b ![1, 0] * (U2 Ω 2 * PkgI1.thetaConst (![1, 0] + a, 0) ((2 : ℂ) • Ω)) +
      dupSign a b ![1, 1] * (U2 Ω 3 * PkgI1.thetaConst (![1, 1] + a, 0) ((2 : ℂ) • Ω)) := by
  rw [thetaConst_sq_eq hΩ, univ_fin2_fin2, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [U2, Matrix.cons_val]; ring

theorem sq0 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![0, 0], ![0, 0]) Ω ^ 2 = U2 Ω 0 ^ 2 + U2 Ω 1 ^ 2 + U2 Ω 2 ^ 2 + U2 Ω 3 ^ 2 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq1 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![0, 0], ![0, 1]) Ω ^ 2 = U2 Ω 0 ^ 2 - U2 Ω 1 ^ 2 + U2 Ω 2 ^ 2 - U2 Ω 3 ^ 2 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq2 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![0, 0], ![1, 0]) Ω ^ 2 = U2 Ω 0 ^ 2 + U2 Ω 1 ^ 2 - U2 Ω 2 ^ 2 - U2 Ω 3 ^ 2 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq3 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![0, 0], ![1, 1]) Ω ^ 2 = U2 Ω 0 ^ 2 - U2 Ω 1 ^ 2 - U2 Ω 2 ^ 2 + U2 Ω 3 ^ 2 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq4 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![0, 1], ![0, 0]) Ω ^ 2 = 2 * U2 Ω 0 * U2 Ω 1 + 2 * U2 Ω 2 * U2 Ω 3 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq5 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![0, 1], ![1, 0]) Ω ^ 2 = 2 * U2 Ω 0 * U2 Ω 1 - 2 * U2 Ω 2 * U2 Ω 3 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq6 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![1, 0], ![0, 0]) Ω ^ 2 = 2 * U2 Ω 0 * U2 Ω 2 + 2 * U2 Ω 1 * U2 Ω 3 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq7 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![1, 0], ![0, 1]) Ω ^ 2 = 2 * U2 Ω 0 * U2 Ω 2 - 2 * U2 Ω 1 * U2 Ω 3 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq8 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![1, 1], ![0, 0]) Ω ^ 2 = 2 * U2 Ω 0 * U2 Ω 3 + 2 * U2 Ω 1 * U2 Ω 2 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq9 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![1, 1], ![1, 1]) Ω ^ 2 = 2 * U2 Ω 0 * U2 Ω 3 - 2 * U2 Ω 1 * U2 Ω 2 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem evenChars_eq : PkgI1.evenChars = {(![0, 0], ![0, 0]), (![0, 0], ![0, 1]), (![0, 0], ![1, 0]), (![0, 0], ![1, 1]), (![0, 1], ![0, 0]), (![0, 1], ![1, 0]), (![1, 0], ![0, 0]), (![1, 0], ![0, 1]), (![1, 1], ![0, 0]), (![1, 1], ![1, 1])} := by decide

theorem sum_evenChars (f : PkgI1.Char2 → ℂ) :
    ∑ m ∈ PkgI1.evenChars, f m = f (![0, 0], ![0, 0]) + f (![0, 0], ![0, 1]) + f (![0, 0], ![1, 0]) + f (![0, 0], ![1, 1]) + f (![0, 1], ![0, 0]) + f (![0, 1], ![1, 0]) + f (![1, 0], ![0, 0]) + f (![1, 0], ![0, 1]) + f (![1, 1], ![0, 0]) + f (![1, 1], ![1, 1]) := by
  rw [evenChars_eq]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton, not_false_eq_true]
  ring

theorem pow16_of_sq {x q : ℂ} (h : x ^ 2 = q) : x ^ 16 = q ^ 8 := by rw [← h]; ring
theorem pow8_of_sq {x q : ℂ} (h : x ^ 2 = q) : x ^ 8 = q ^ 4 := by rw [← h]; ring

theorem thetaEightSquare' (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    ∑ m ∈ PkgI1.evenChars, PkgI1.thetaConst m Ω ^ 16 =
      (∑ m ∈ PkgI1.evenChars, PkgI1.thetaConst m Ω ^ 8) ^ 2 / 4 := by
  rw [sum_evenChars, sum_evenChars]
  rw [pow16_of_sq (sq0 hΩ), pow8_of_sq (sq0 hΩ), pow16_of_sq (sq1 hΩ), pow8_of_sq (sq1 hΩ), pow16_of_sq (sq2 hΩ), pow8_of_sq (sq2 hΩ), pow16_of_sq (sq3 hΩ), pow8_of_sq (sq3 hΩ), pow16_of_sq (sq4 hΩ), pow8_of_sq (sq4 hΩ), pow16_of_sq (sq5 hΩ), pow8_of_sq (sq5 hΩ), pow16_of_sq (sq6 hΩ), pow8_of_sq (sq6 hΩ), pow16_of_sq (sq7 hΩ), pow8_of_sq (sq7 hΩ), pow16_of_sq (sq8 hΩ), pow8_of_sq (sq8 hΩ), pow16_of_sq (sq9 hΩ), pow8_of_sq (sq9 hΩ)]
  ring


/-! ## 3. `ThetaEightSquare` -/

/-- **`ThetaEightSquare` (proved).** -/
theorem thetaEightSquare : ThetaEightSquare := thetaEightSquare'

/-! ## 4. Igusa's theta expressions (Igusa, Amer. J. Math. 89 (1967); locators UNVERIFIED)

`ψ₄ = 2⁻² Σ_m θ_m⁸`, `ψ₆ = 2⁻² Σ_{syzygous {m₁,m₂,m₃}} ±(θ_{m₁}θ_{m₂}θ_{m₃})⁴` (60 triples),
`χ₁₀ = −2⁻¹⁴ ∏_m θ_m²`, `χ₁₂ = 2⁻¹⁷3⁻¹ Σ_{Göpel quadruples Q} ∏_{m ∉ Q} θ_m⁴` (15 quadruples).
The signs in `ψ₆` are the ones forced by `Sp₄(ℤ)`-modularity (scratch/theta-glue/py/signs.py: the ten
`θ_m⁴` are permuted with signs by generators of `Sp₄(ℤ)`, which act transitively on the 60 syzygous
triples); with them the expression is exactly the weight-6 Siegel modular form with constant term 1
and restriction `E₆⊗E₆` to `diag(τ₁, τ₂)`. The `χ₁₂` expression is exactly the weight-12 cusp form with
restriction `Δ⊗Δ` (py/igusa2.py, exact). -/

/-- Igusa's `ψ₄ = 2⁻² Σ_{m even} θ_m⁸`. -/
def psi4Th (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := PkgI1.thetaSum8 Ω / 4

/-- Igusa's `χ₁₀ = −2⁻¹⁴ ∏_{m even} θ_m²`. -/
def chi10Th (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := -PkgI1.thetaProd2 Ω / 2 ^ 14

/-- Igusa's `ψ₆ = 2⁻² Σ_{syzygous} ±(θ_{m₁}θ_{m₂}θ_{m₃})⁴`. -/
def psi6Th (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (1 / 4) * ((PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4)

/-- `ψ₆` as a function of the squares `t_m = θ_m²`. -/
def psi6T (t : PkgI1.Char2 → ℂ) : ℂ :=
  (1 / 4) * ((t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 0])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 1]) * t (![1, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 1]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0])) ^ 2
     + (t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 1])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![1, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 2
     + (t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 2
     - (t (![0, 0], ![1, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 2)

/-- Igusa's `χ₁₂ = 2⁻¹⁷3⁻¹ Σ_{Göpel Q} ∏_{m∉Q} θ_m⁴`. -/
def chi12Th (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (1 / (2 ^ 17 * 3)) * ((PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4)

/-- `χ₁₂` as a function of the squares `t_m = θ_m²`. -/
def chi12T (t : PkgI1.Char2 → ℂ) : ℂ :=
  (1 / (2 ^ 17 * 3)) * ((t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 2
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 2)

/-- `ψ₄` as a function of the squares `t_m = θ_m²`. -/
def psi4T (t : PkgI1.Char2 → ℂ) : ℂ := (∑ m ∈ PkgI1.evenChars, t m ^ 4) / 4

/-- `χ₁₀` as a function of the squares `t_m = θ_m²`. -/
def chi10T (t : PkgI1.Char2 → ℂ) : ℂ := -(∏ m ∈ PkgI1.evenChars, t m) / 2 ^ 14

/-! ## 5. The LEAF and the reduction of `QMThetaSymmetricCurve` -/

/-- **LEAF, COMPOSITE (Lin–Yang's Igusa vector on the QM curve, in Igusa's theta expressions, along
the explicit curve `τ ↦ Ω(τ)`).** For `τ` in the upper half-plane, at `Ω = Ω(τ)` (pkg-I1's period
matrix of the principally polarized QM surface `ℂ²/ι(𝒪)(τ,1)ᵀ`, `𝒪` the maximal order of the
quaternion algebra of discriminant 6):
`ψ₄ψ₆ = 2¹²3⁵χ₁₀` and `ψ₄³ + ψ₆² = 2¹²3⁶χ₁₂`.

Sources: Lin–Yang, *Quaternionic loci in Siegel's modular threefold*, Math. Z. 295 (2020); arXiv
1807.00466v1, Example 29 with eqs. (13)-(14): along the curve `s₃²/s₂³ = c₁j`, `s₅/(s₂s₃) = c₂`,
`s₆/s₂³ = c₃j + c₄` for Igusa's `s₂ = ψ₄, s₃ = ψ₆, s₅ = 2¹²3⁵χ₁₀, s₆ = 2¹²3⁶χ₁₂`, with
`c₁ = c₂ = c₃ = c₄ = 1` in the normalization of `j` fixed at the CM points of discriminants −4, −24
(as restated in scratch/h-v14/igusa_check.py; locators UNVERIFIED here); eliminating `j` gives the two
relations, so the statement is weaker than the printed one. Igusa, *Modular forms and projective
invariants*, Amer. J. Math. 89 (1967) for the theta expressions (§4). Faithfulness: the same
identification of `Ω(τ)` with the QM locus as `PkgI1.QMHauptmodul` (pkg-I1 §4). Numerically VERIFIED
(py/curve_check.py, 80 digits, 12 random `τ`: relative residuals ≤ 9e-78 and ≤ 5e-75). -/
def LinYangThetaCurve : Prop :=
  ∀ τ : ℂ, 0 < τ.im →
    psi4Th (PkgI1.Omega τ) * psi6Th (PkgI1.Omega τ) = 2 ^ 12 * 3 ^ 5 * chi10Th (PkgI1.Omega τ) ∧
    psi4Th (PkgI1.Omega τ) ^ 3 + psi6Th (PkgI1.Omega τ) ^ 2 = 2 ^ 12 * 3 ^ 6 * chi12Th (PkgI1.Omega τ)

/-- The polynomials `P_k` with `e_k(θ_m⁸) = P_k(ψ₄, ψ₆, χ₁₀, χ₁₂)` (py/pk.py, exact). -/
def igusaP : ℕ → ℂ → ℂ → ℂ → ℂ → ℂ
  | 3, a, b, _, d => (1081344 : ℂ) * d + (-8 / 27 : ℂ) * b ^ 2 + (116 / 27 : ℂ) * a ^ 3
  | 4, a, b, c, d => (-262144 / 3 : ℂ) * b * c + (1507328 : ℂ) * a * d + (-16 / 27 : ℂ) * a * b ^ 2 + (43 / 27 : ℂ) * a ^ 4
  | 5, a, b, c, d => (33017561088 : ℂ) * c ^ 2 + (131072 / 3 : ℂ) * a * b * c + (819200 : ℂ) * a ^ 2 * d + (-8 / 27 : ℂ) * a ^ 2 * b ^ 2 + (8 / 27 : ℂ) * a ^ 5
  | 6, a, b, c, d => (34628173824 : ℂ) * d ^ 2 + (-655360 / 9 : ℂ) * b ^ 2 * d + (16 / 729 : ℂ) * b ^ 4 + (50465865728 / 3 : ℂ) * a * c ^ 2 + (131072 / 3 : ℂ) * a ^ 2 * b * c + (1835008 / 9 : ℂ) * a ^ 3 * d + (-32 / 729 : ℂ) * a ^ 3 * b ^ 2 + (16 / 729 : ℂ) * a ^ 6
  | 7, a, b, c, d => (40802189312 / 3 : ℂ) * b * c * d + (-524288 / 81 : ℂ) * b ^ 3 * c + (23622320128 : ℂ) * a * d ^ 2 + (-524288 / 27 : ℂ) * a * b ^ 2 * d + (22011707392 / 9 : ℂ) * a ^ 2 * c ^ 2 + (524288 / 81 : ℂ) * a ^ 3 * b * c + (524288 / 27 : ℂ) * a ^ 4 * d
  | 8, a, b, c, d => (-290271069732864 : ℂ) * c ^ 2 * d + (10737418240 / 27 : ℂ) * b ^ 2 * c ^ 2 + (8589934592 / 3 : ℂ) * a * b * c * d + (4294967296 : ℂ) * a ^ 2 * d ^ 2 + (2147483648 / 27 : ℂ) * a ^ 3 * c ^ 2
  | 9, a, b, c, d => (281474976710656 : ℂ) * d ^ 3 + (-246290604621824 / 27 : ℂ) * b * c ^ 3 + (-175921860444160 / 3 : ℂ) * a * c ^ 2 * d
  | _, _, _, _, _ => 0


/-- **GLUE (global identities of Siegel modular forms of genus 2, `3 ≤ k ≤ 9`).** For `Ω ∈ 𝔥₂`, the
`k`-th elementary symmetric function of the ten `θ_m(Ω)⁸` is `P_k(ψ₄, ψ₆, χ₁₀, χ₁₂)` (Igusa's theta
expressions). Why true: both sides are modular forms of weight `4k` (Igusa's structure theorem gives
existence of `P_k`); here it is reduced to closed polynomial identities in the four second-order theta
constants (`igusaThetaSymmetric_of_alg`), VERIFIED by exact expansion (py/verify_pk.py). -/
def IgusaThetaSymmetric : Prop :=
  ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → ∀ k, 3 ≤ k → k ≤ 9 →
    (thetaEight Ω).esymm k = igusaP k (psi4Th Ω) (psi6Th Ω) (chi10Th Ω) (chi12Th Ω)

/-- `j_θ = ψ₆²/ψ₄³` from `ψ₄ψ₆ = 2¹²3⁵χ₁₀`. -/
theorem jratio_eq {Ω : Matrix (Fin 2) (Fin 2) ℂ} (ha : psi4Th Ω ≠ 0)
    (h1 : psi4Th Ω * psi6Th Ω = 2 ^ 12 * 3 ^ 5 * chi10Th Ω) :
    PkgI1.jNum Ω / PkgI1.jDen Ω = psi6Th Ω ^ 2 / psi4Th Ω ^ 3 := by
  have hS : PkgI1.thetaSum8 Ω = 4 * psi4Th Ω := by unfold psi4Th; ring
  have hP : PkgI1.thetaProd2 Ω = -2 ^ 14 * chi10Th Ω := by unfold chi10Th; ring
  rw [PkgI1.jNum, PkgI1.jDen, hS, hP]
  have hc : chi10Th Ω = psi4Th Ω * psi6Th Ω / (2 ^ 12 * 3 ^ 5) := by
    rw [h1]; field_simp
  rw [hc]
  field_simp
  ring

/-- **`QMThetaSymmetricCurve` from the LEAF and the GLUE (proved).** -/
theorem qmThetaSymmetricCurve_of (hL : LinYangThetaCurve) (hG : IgusaThetaSymmetric) :
    QMThetaSymmetricCurve := by
  intro τ hτ hS k hk3 hk9
  have hΩ : IsSiegel (PkgI1.Omega τ) := isSiegel_Omega hτ
  rw [hG _ hΩ k hk3 hk9]
  obtain ⟨h1, h2⟩ := hL τ hτ
  have ha : psi4Th (PkgI1.Omega τ) ≠ 0 := by
    unfold psi4Th; exact div_ne_zero hS (by norm_num)
  rw [jratio_eq ha h1]
  have hS4 : PkgI1.thetaSum8 (PkgI1.Omega τ) = 4 * psi4Th (PkgI1.Omega τ) := by unfold psi4Th; ring
  have hc : chi10Th (PkgI1.Omega τ) =
      psi4Th (PkgI1.Omega τ) * psi6Th (PkgI1.Omega τ) / (2 ^ 12 * 3 ^ 5) := by
    rw [h1]; field_simp
  have hd : chi12Th (PkgI1.Omega τ) =
      (psi4Th (PkgI1.Omega τ) ^ 3 + psi6Th (PkgI1.Omega τ) ^ 2) / (2 ^ 12 * 3 ^ 6) := by
    rw [h2]; field_simp
  rw [hS4, hc, hd]
  generalize psi4Th (PkgI1.Omega τ) = a at ha ⊢
  generalize psi6Th (PkgI1.Omega τ) = b
  interval_cases k <;> simp [igusaP, qmR] <;> field_simp <;> ring

/-! ## 6. Reduction of `IgusaThetaSymmetric` to polynomial identities (duplication formula) -/

/-- The square `θ_m² = Σ_c (−1)^{(c+a)·b} U_c U_{c+a}` as a polynomial in the four second-order theta
constants `U_c = θ[c;0](2Ω)` (`thetaConst_sq_eq`). -/
def Sq (m : PkgI1.Char2) (u : (Fin 2 → Fin 2) → ℂ) : ℂ :=
  ∑ c : Fin 2 → Fin 2, (-1 : ℂ) ^ ((((c + m.1) 0 : Fin 2) : ℕ) * (m.2 0 : ℕ) +
    (((c + m.1) 1 : Fin 2) : ℕ) * (m.2 1 : ℕ)) * (u c * u (c + m.1))

theorem sq_eq_Sq {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : IsSiegel Ω) (m : PkgI1.Char2) :
    PkgI1.thetaConst m Ω ^ 2 = Sq m (fun c => PkgI1.thetaConst (c, 0) ((2 : ℂ) • Ω)) := by
  rw [show m = (m.1, m.2) from rfl, thetaConst_sq_eq hΩ]
  simp only [Sq, dupSign_eq]

/-- **GLUE (closed polynomial identity, weight `4k`; VERIFIED by exact expansion, py/verify_pk.py).**
For all `u : {0,1}² → ℂ`, with `t_m = Sq m u`: `e_k(t_m⁴) = P_k(ψ₄(t), ψ₆(t), χ₁₀(t), χ₁₂(t))`. -/
def IgusaAlg (k : ℕ) : Prop :=
  ∀ u : (Fin 2 → Fin 2) → ℂ,
    (PkgI1.evenChars.val.map (fun m => Sq m u ^ 4)).esymm k =
      igusaP k (psi4T (fun m => Sq m u)) (psi6T (fun m => Sq m u)) (chi10T (fun m => Sq m u))
        (chi12T (fun m => Sq m u))

theorem psi4Th_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    psi4Th Ω = psi4T (fun m => PkgI1.thetaConst m Ω ^ 2) := by
  simp only [psi4Th, psi4T, PkgI1.thetaSum8]
  congr 1
  exact Finset.sum_congr rfl fun m _ => by ring

theorem chi10Th_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    chi10Th Ω = chi10T (fun m => PkgI1.thetaConst m Ω ^ 2) := rfl

theorem psi6Th_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    psi6Th Ω = psi6T (fun m => PkgI1.thetaConst m Ω ^ 2) := by
  simp only [psi6Th, psi6T]; ring

theorem chi12Th_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    chi12Th Ω = chi12T (fun m => PkgI1.thetaConst m Ω ^ 2) := by
  simp only [chi12Th, chi12T]; ring

theorem thetaEight_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    thetaEight Ω = PkgI1.evenChars.val.map (fun m => (PkgI1.thetaConst m Ω ^ 2) ^ 4) := by
  unfold thetaEight
  exact Multiset.map_congr rfl fun m _ => by ring

/-- **`IgusaThetaSymmetric` from the polynomial identities (proved).** -/
theorem igusaThetaSymmetric_of_alg (h : ∀ k, 3 ≤ k → k ≤ 9 → IgusaAlg k) : IgusaThetaSymmetric := by
  intro Ω hΩ k hk3 hk9
  rw [thetaEight_eq, psi4Th_eq, psi6Th_eq, chi10Th_eq, chi12Th_eq]
  simp only [sq_eq_Sq hΩ]
  exact h k hk3 hk9 _

/-- **Route 1 for `QMThetaSymmetricCurve`, final form (proved):** the LEAF and seven closed polynomial
identities. -/
theorem qmThetaSymmetricCurve_of_alg (hL : LinYangThetaCurve)
    (h : ∀ k, 3 ≤ k → k ≤ 9 → IgusaAlg k) : QMThetaSymmetricCurve :=
  qmThetaSymmetricCurve_of hL (igusaThetaSymmetric_of_alg h)


/-! ## 7. `IgusaAlg 3` and `IgusaAlg 4` proved by `ring`

The multiset is unfolded to an explicit list (`evenChars_val`, by `decide`) and `Multiset.esymm` to the
recursion `esymmL`; the ten `Sq` become explicit quadratics (`Sq0`..`Sq9`); then one `ring` (degree 24,
resp. 32, in four variables). `IgusaAlg 5`..`IgusaAlg 9` (degrees 40-72) are beyond this method within
the 24 GB memory budget (docs/research/theta-glue.md §4); they are VERIFIED by exact expansion
(py/verify_pk.py). -/

def esymmL : List ℂ → ℕ → ℂ
  | _, 0 => 1
  | [], _ + 1 => 0
  | a :: l, k + 1 => esymmL l (k + 1) + a * esymmL l k

theorem esymm_coe (l : List ℂ) (k : ℕ) : (l : Multiset ℂ).esymm k = esymmL l k := by
  induction l generalizing k with
  | nil => cases k <;> simp [esymmL, Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a l ih =>
    cases k with
    | zero => simp [esymmL, Multiset.esymm]
    | succ k => rw [← Multiset.cons_coe, esymm_cons_succ, ih, ih, esymmL]

theorem evenChars_val : PkgI1.evenChars.val = (([(![0, 0], ![0, 0]), (![0, 0], ![0, 1]),
    (![0, 0], ![1, 0]), (![0, 0], ![1, 1]), (![0, 1], ![0, 0]), (![0, 1], ![1, 0]),
    (![1, 0], ![0, 0]), (![1, 0], ![0, 1]), (![1, 1], ![0, 0]), (![1, 1], ![1, 1])] : List PkgI1.Char2) : Multiset PkgI1.Char2) := by decide


theorem Sq0 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![0, 0], ![0, 0]) u = u ![0, 0] ^ 2 + u ![0, 1] ^ 2 + u ![1, 0] ^ 2 + u ![1, 1] ^ 2 := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq1 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![0, 0], ![0, 1]) u = u ![0, 0] ^ 2 - u ![0, 1] ^ 2 + u ![1, 0] ^ 2 - u ![1, 1] ^ 2 := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq2 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![0, 0], ![1, 0]) u = u ![0, 0] ^ 2 + u ![0, 1] ^ 2 - u ![1, 0] ^ 2 - u ![1, 1] ^ 2 := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq3 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![0, 0], ![1, 1]) u = u ![0, 0] ^ 2 - u ![0, 1] ^ 2 - u ![1, 0] ^ 2 + u ![1, 1] ^ 2 := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq4 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![0, 1], ![0, 0]) u = 2 * u ![0, 0] * u ![0, 1] + 2 * u ![1, 0] * u ![1, 1] := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq5 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![0, 1], ![1, 0]) u = 2 * u ![0, 0] * u ![0, 1] - 2 * u ![1, 0] * u ![1, 1] := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq6 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![1, 0], ![0, 0]) u = 2 * u ![0, 0] * u ![1, 0] + 2 * u ![0, 1] * u ![1, 1] := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq7 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![1, 0], ![0, 1]) u = 2 * u ![0, 0] * u ![1, 0] - 2 * u ![0, 1] * u ![1, 1] := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq8 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![1, 1], ![0, 0]) u = 2 * u ![0, 0] * u ![1, 1] + 2 * u ![0, 1] * u ![1, 0] := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem Sq9 (u : (Fin 2 → Fin 2) → ℂ) :
    Sq (![1, 1], ![1, 1]) u = 2 * u ![0, 0] * u ![1, 1] - 2 * u ![0, 1] * u ![1, 0] := by
  rw [Sq, univ_fin2_fin2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

theorem prod_evenChars (f : PkgI1.Char2 → ℂ) :
    ∏ m ∈ PkgI1.evenChars, f m = f (![0, 0], ![0, 0]) * f (![0, 0], ![0, 1]) * f (![0, 0], ![1, 0]) * f (![0, 0], ![1, 1]) * f (![0, 1], ![0, 0]) * f (![0, 1], ![1, 0]) * f (![1, 0], ![0, 0]) * f (![1, 0], ![0, 1]) * f (![1, 1], ![0, 0]) * f (![1, 1], ![1, 1]) := by
  rw [evenChars_eq]
  simp (config := {decide := true}) only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.prod_singleton, not_false_eq_true]
  ring


section IgusaAlgKron

/-! ## igusa-alg: `IgusaAlg k` from the Kronecker-checked identities in `s_i = U_i²` -/

open IgusaAlgEval

theorem esymmL_nil (j : ℕ) : esymmL [] j = E ([] : List (ℂ × ℂ)) j := by cases j <;> rfl

theorem esymmL_single {l : List ℂ} {bl : List (ℂ × ℂ)} (h : ∀ j, esymmL l j = E bl j) (a : ℂ) :
    ∀ j, esymmL (a :: l) j = E ((a, 0) :: bl) j := by
  intro j
  cases j with
  | zero => simp [esymmL, E, ← h 0]
  | succ j => simp [esymmL, E, h]

theorem esymmL_pair {l : List ℂ} {bl : List (ℂ × ℂ)} (h : ∀ j, esymmL l j = E bl j) (a b : ℂ) :
    ∀ j, esymmL (a :: b :: l) j = E ((a + b, a * b) :: bl) j := by
  intro j
  rcases j with _ | _ | j
  · simp [esymmL, E, ← h 0]
  · simp [esymmL, E, ← h 0, ← h 1]; ring
  · simp [esymmL, E, h]; ring

theorem esymmL_blocks (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : ℂ) (k : ℕ) :
    esymmL [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] k =
      E [(a0, 0), (a1, 0), (a2, 0), (a3, 0), (a4 + a5, a4 * a5), (a6 + a7, a6 * a7), (a8 + a9, a8 * a9)] k :=
  esymmL_single (esymmL_single (esymmL_single (esymmL_single (esymmL_pair (esymmL_pair
    (esymmL_pair esymmL_nil a8 a9) a6 a7) a4 a5) a3) a2) a1) a0 k

set_option maxHeartbeats 4000000 in
theorem blocks_eval (x0 x1 x2 x3 : ℂ) :
    blocksPE.map (evB (x0 ^ 2) (x1 ^ 2) (x2 ^ 2) (x3 ^ 2)) =
      [((x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2) ^ 4, 0), ((x0 ^ 2 - x1 ^ 2 + x2 ^ 2 - x3 ^ 2) ^ 4, 0),
       ((x0 ^ 2 + x1 ^ 2 - x2 ^ 2 - x3 ^ 2) ^ 4, 0), ((x0 ^ 2 - x1 ^ 2 - x2 ^ 2 + x3 ^ 2) ^ 4, 0),
       ((2 * x0 * x1 + 2 * x2 * x3) ^ 4 + (2 * x0 * x1 - 2 * x2 * x3) ^ 4,
         (2 * x0 * x1 + 2 * x2 * x3) ^ 4 * (2 * x0 * x1 - 2 * x2 * x3) ^ 4),
       ((2 * x0 * x2 + 2 * x1 * x3) ^ 4 + (2 * x0 * x2 - 2 * x1 * x3) ^ 4,
         (2 * x0 * x2 + 2 * x1 * x3) ^ 4 * (2 * x0 * x2 - 2 * x1 * x3) ^ 4),
       ((2 * x0 * x3 + 2 * x1 * x2) ^ 4 + (2 * x0 * x3 - 2 * x1 * x2) ^ 4,
         (2 * x0 * x3 + 2 * x1 * x2) ^ 4 * (2 * x0 * x3 - 2 * x1 * x2) ^ 4)] := by
  simp only [blocksPE, List.map_cons, List.map_nil, evB, blkQ0, blkQ1, blkQ2, blkQ3, blkQ4, blkQ5,
    blkQ6, blkR0, blkR1, blkR2, blkR3, blkR4, blkR5, blkR6, PE.eval, PE.eval_v0, PE.eval_v1,
    PE.eval_v2, PE.eval_v3, List.cons.injEq, Prod.mk.injEq, and_true]
  push_cast
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> ring

set_option maxHeartbeats 4000000 in
theorem psi4T_eq (u : (Fin 2 → Fin 2) → ℂ) : psi4T (fun m => Sq m u) =
    psi4E.eval (u ![0, 0] ^ 2) (u ![0, 1] ^ 2) (u ![1, 0] ^ 2) (u ![1, 1] ^ 2) / 4 := by
  simp only [psi4T, sum_evenChars, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9, psi4E, PE.eval,
    PE.eval_v0, PE.eval_v1, PE.eval_v2, PE.eval_v3]
  generalize u ![0, 0] = x0; generalize u ![0, 1] = x1
  generalize u ![1, 0] = x2; generalize u ![1, 1] = x3
  push_cast; ring

set_option maxHeartbeats 4000000 in
theorem psi6T_eq (u : (Fin 2 → Fin 2) → ℂ) : psi6T (fun m => Sq m u) =
    psi6E.eval (u ![0, 0] ^ 2) (u ![0, 1] ^ 2) (u ![1, 0] ^ 2) (u ![1, 1] ^ 2) / 4 := by
  simp only [psi6T, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9, psi6E, PE.eval,
    PE.eval_v0, PE.eval_v1, PE.eval_v2, PE.eval_v3]
  generalize u ![0, 0] = x0; generalize u ![0, 1] = x1
  generalize u ![1, 0] = x2; generalize u ![1, 1] = x3
  push_cast; ring

set_option maxHeartbeats 4000000 in
theorem chi10T_eq (u : (Fin 2 → Fin 2) → ℂ) : chi10T (fun m => Sq m u) =
    -(x10E.eval (u ![0, 0] ^ 2) (u ![0, 1] ^ 2) (u ![1, 0] ^ 2) (u ![1, 1] ^ 2)) / 2 ^ 14 := by
  simp only [chi10T, prod_evenChars, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9, x10E, PE.eval,
    PE.eval_v0, PE.eval_v1, PE.eval_v2, PE.eval_v3]
  generalize u ![0, 0] = x0; generalize u ![0, 1] = x1
  generalize u ![1, 0] = x2; generalize u ![1, 1] = x3
  push_cast; ring

set_option maxHeartbeats 0 in
theorem chi12T_eq (u : (Fin 2 → Fin 2) → ℂ) : chi12T (fun m => Sq m u) =
    x12E.eval (u ![0, 0] ^ 2) (u ![0, 1] ^ 2) (u ![1, 0] ^ 2) (u ![1, 1] ^ 2) / (2 ^ 17 * 3) := by
  simp only [chi12T, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9, x12E, x12E0, x12E1, x12E2,
    x12E3, PE.eval, PE.eval_v0, PE.eval_v1, PE.eval_v2, PE.eval_v3]
  generalize u ![0, 0] = x0; generalize u ![0, 1] = x1
  generalize u ![1, 0] = x2; generalize u ![1, 1] = x3
  push_cast; ring

theorem igusaAlg_of_data (k : ℕ) (X : Data) (hk : X.k = k) (hb : X.blocks = blocksPE) (hD : X.dK ≠ 0)
    (hgen : ∀ s0 s1 s2 s3 : ℂ, X.gen s0 s1 s2 s3 = 0)
    (hrhs : ∀ s0 s1 s2 s3 : ℂ, X.rhs.eval s0 s1 s2 s3 = (X.dK : ℂ) *
      igusaP k (psi4E.eval s0 s1 s2 s3 / 4) (psi6E.eval s0 s1 s2 s3 / 4)
        (-(x10E.eval s0 s1 s2 s3) / 2 ^ 14) (x12E.eval s0 s1 s2 s3 / (2 ^ 17 * 3))) :
    IgusaAlg k := by
  intro u
  have h := hgen (u ![0, 0] ^ 2) (u ![0, 1] ^ 2) (u ![1, 0] ^ 2) (u ![1, 1] ^ 2)
  rw [Data.gen, hrhs, hb, hk, sub_eq_zero, blocks_eval] at h
  rw [psi4T_eq, psi6T_eq, chi10T_eq, chi12T_eq, evenChars_val, Multiset.map_coe, esymm_coe]
  simp only [List.map, Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9]
  rw [esymmL_blocks]
  exact mul_left_cancel₀ (Int.cast_ne_zero.mpr hD) h

set_option maxHeartbeats 4000000 in
theorem rhs3_eq (s0 s1 s2 s3 : ℂ) : rhsE3.eval s0 s1 s2 s3 = ((dK3 : ℤ) : ℂ) *
    igusaP 3 (psi4E.eval s0 s1 s2 s3 / 4) (psi6E.eval s0 s1 s2 s3 / 4)
      (-(x10E.eval s0 s1 s2 s3) / 2 ^ 14) (x12E.eval s0 s1 s2 s3 / (2 ^ 17 * 3)) := by
  simp only [rhsE3, dK3, PE.eval, igusaP]
  push_cast; ring

/-- **`IgusaAlg 3` (theta-glue's GLUE), proved.** -/
theorem igusaAlg3 : IgusaAlg 3 :=
  igusaAlg_of_data 3 data3 rfl rfl (by decide) (fun s0 s1 s2 s3 => gen3_eq_zero s0 s1 s2 s3)
    (fun s0 s1 s2 s3 => rhs3_eq s0 s1 s2 s3)

set_option maxHeartbeats 4000000 in
theorem rhs4_eq (s0 s1 s2 s3 : ℂ) : rhsE4.eval s0 s1 s2 s3 = ((dK4 : ℤ) : ℂ) *
    igusaP 4 (psi4E.eval s0 s1 s2 s3 / 4) (psi6E.eval s0 s1 s2 s3 / 4)
      (-(x10E.eval s0 s1 s2 s3) / 2 ^ 14) (x12E.eval s0 s1 s2 s3 / (2 ^ 17 * 3)) := by
  simp only [rhsE4, dK4, PE.eval, igusaP]
  push_cast; ring

/-- **`IgusaAlg 4` (theta-glue's GLUE), proved.** -/
theorem igusaAlg4 : IgusaAlg 4 :=
  igusaAlg_of_data 4 data4 rfl rfl (by decide) (fun s0 s1 s2 s3 => gen4_eq_zero s0 s1 s2 s3)
    (fun s0 s1 s2 s3 => rhs4_eq s0 s1 s2 s3)

set_option maxHeartbeats 4000000 in
theorem rhs5_eq (s0 s1 s2 s3 : ℂ) : rhsE5.eval s0 s1 s2 s3 = ((dK5 : ℤ) : ℂ) *
    igusaP 5 (psi4E.eval s0 s1 s2 s3 / 4) (psi6E.eval s0 s1 s2 s3 / 4)
      (-(x10E.eval s0 s1 s2 s3) / 2 ^ 14) (x12E.eval s0 s1 s2 s3 / (2 ^ 17 * 3)) := by
  simp only [rhsE5, dK5, PE.eval, igusaP]
  push_cast; ring

/-- **`IgusaAlg 5` (theta-glue's GLUE), proved.** -/
theorem igusaAlg5 : IgusaAlg 5 :=
  igusaAlg_of_data 5 data5 rfl rfl (by decide) (fun s0 s1 s2 s3 => gen5_eq_zero s0 s1 s2 s3)
    (fun s0 s1 s2 s3 => rhs5_eq s0 s1 s2 s3)

set_option maxHeartbeats 4000000 in
theorem rhs6_eq (s0 s1 s2 s3 : ℂ) : rhsE6.eval s0 s1 s2 s3 = ((dK6 : ℤ) : ℂ) *
    igusaP 6 (psi4E.eval s0 s1 s2 s3 / 4) (psi6E.eval s0 s1 s2 s3 / 4)
      (-(x10E.eval s0 s1 s2 s3) / 2 ^ 14) (x12E.eval s0 s1 s2 s3 / (2 ^ 17 * 3)) := by
  simp only [rhsE6, dK6, PE.eval, igusaP]
  push_cast; ring

/-- **`IgusaAlg 6` (theta-glue's GLUE), proved.** -/
theorem igusaAlg6 : IgusaAlg 6 :=
  igusaAlg_of_data 6 data6 rfl rfl (by decide) (fun s0 s1 s2 s3 => gen6_eq_zero s0 s1 s2 s3)
    (fun s0 s1 s2 s3 => rhs6_eq s0 s1 s2 s3)

set_option maxHeartbeats 4000000 in
theorem rhs7_eq (s0 s1 s2 s3 : ℂ) : rhsE7.eval s0 s1 s2 s3 = ((dK7 : ℤ) : ℂ) *
    igusaP 7 (psi4E.eval s0 s1 s2 s3 / 4) (psi6E.eval s0 s1 s2 s3 / 4)
      (-(x10E.eval s0 s1 s2 s3) / 2 ^ 14) (x12E.eval s0 s1 s2 s3 / (2 ^ 17 * 3)) := by
  simp only [rhsE7, dK7, PE.eval, igusaP]
  push_cast; ring

/-- **`IgusaAlg 7` (theta-glue's GLUE), proved.** -/
theorem igusaAlg7 : IgusaAlg 7 :=
  igusaAlg_of_data 7 data7 rfl rfl (by decide) (fun s0 s1 s2 s3 => gen7_eq_zero s0 s1 s2 s3)
    (fun s0 s1 s2 s3 => rhs7_eq s0 s1 s2 s3)

set_option maxHeartbeats 4000000 in
theorem rhs8_eq (s0 s1 s2 s3 : ℂ) : rhsE8.eval s0 s1 s2 s3 = ((dK8 : ℤ) : ℂ) *
    igusaP 8 (psi4E.eval s0 s1 s2 s3 / 4) (psi6E.eval s0 s1 s2 s3 / 4)
      (-(x10E.eval s0 s1 s2 s3) / 2 ^ 14) (x12E.eval s0 s1 s2 s3 / (2 ^ 17 * 3)) := by
  simp only [rhsE8, dK8, PE.eval, igusaP]
  push_cast; ring

/-- **`IgusaAlg 8` (theta-glue's GLUE), proved.** -/
theorem igusaAlg8 : IgusaAlg 8 :=
  igusaAlg_of_data 8 data8 rfl rfl (by decide) (fun s0 s1 s2 s3 => gen8_eq_zero s0 s1 s2 s3)
    (fun s0 s1 s2 s3 => rhs8_eq s0 s1 s2 s3)

set_option maxHeartbeats 4000000 in
theorem rhs9_eq (s0 s1 s2 s3 : ℂ) : rhsE9.eval s0 s1 s2 s3 = ((dK9 : ℤ) : ℂ) *
    igusaP 9 (psi4E.eval s0 s1 s2 s3 / 4) (psi6E.eval s0 s1 s2 s3 / 4)
      (-(x10E.eval s0 s1 s2 s3) / 2 ^ 14) (x12E.eval s0 s1 s2 s3 / (2 ^ 17 * 3)) := by
  simp only [rhsE9, dK9, PE.eval, igusaP]
  push_cast; ring

/-- **`IgusaAlg 9` (theta-glue's GLUE), proved.** -/
theorem igusaAlg9 : IgusaAlg 9 :=
  igusaAlg_of_data 9 data9 rfl rfl (by decide) (fun s0 s1 s2 s3 => gen9_eq_zero s0 s1 s2 s3)
    (fun s0 s1 s2 s3 => rhs9_eq s0 s1 s2 s3)

end IgusaAlgKron

/-- **Route 1 for `QMThetaSymmetricCurve` with `k = 3, 4` discharged (proved):** the LEAF and the five
closed polynomial identities `IgusaAlg 5..9`. -/
theorem qmThetaSymmetricCurve_of_alg59 (hL : LinYangThetaCurve)
    (h : ∀ k, 5 ≤ k → k ≤ 9 → IgusaAlg k) : QMThetaSymmetricCurve :=
  qmThetaSymmetricCurve_of_alg hL fun k h3 h9 => by
    rcases (by omega : k = 3 ∨ k = 4 ∨ 5 ≤ k) with rfl | rfl | h5
    · exact igusaAlg3
    · exact igusaAlg4
    · exact h k h5 h9

end HDec.HSyn.G0Split.ThetaPt.ThetaGlue

/-! ## igusa-alg: final theorems -/

namespace HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal

open ThetaGlue ThetaSplit

/-- **All seven closed identities `IgusaAlg 3..9`, proved** (Kronecker evaluation, `IgusaAlgEval`). -/
theorem igusaAlg_all : ∀ k, 3 ≤ k → k ≤ 9 → ThetaGlue.IgusaAlg k := by
  intro k h3 h9
  interval_cases k
  · exact igusaAlg3
  · exact igusaAlg4
  · exact igusaAlg5
  · exact igusaAlg6
  · exact igusaAlg7
  · exact igusaAlg8
  · exact igusaAlg9

/-- theta-glue's verbatim copies agree with theta-split's originals. -/
theorem qmThetaSymmetricCurve_iff : ThetaGlue.QMThetaSymmetricCurve ↔ ThetaSplit.QMThetaSymmetricCurve :=
  Iff.rfl

theorem thetaEightSquare_iff : ThetaGlue.ThetaEightSquare ↔ ThetaSplit.ThetaEightSquare := Iff.rfl

/-- **`QMThetaSymmetricCurve` from the LEAF `LinYangThetaCurve` alone (proved).** -/
theorem qmThetaSymmetricCurve_of_linYang (hL : LinYangThetaCurve) : ThetaSplit.QMThetaSymmetricCurve :=
  qmThetaSymmetricCurve_iff.mp
    (qmThetaSymmetricCurve_of_alg59 hL fun k h5 h9 => igusaAlg_all k (by omega) h9)

/-- **theta-split's core from `LinYangThetaCurve` alone (proved).** -/
theorem qmThetaSymmetricCore_of_linYang (hL : LinYangThetaCurve) : ThetaSplit.QMThetaSymmetricCore :=
  qmThetaSymmetricCore_of (thetaEightSquare_iff.mp thetaEightSquare) (qmThetaSymmetricCurve_of_linYang hL)

/-- **The use form of the field `thetaRatiosAlgebraic` (theta-split's `ThetaRatiosAtQM`) from
`LinYangThetaCurve` alone (proved).** -/
theorem thetaRatiosAtQM_of_linYang (hL : LinYangThetaCurve) : ThetaRatiosAtQM :=
  thetaRatiosAtQM_of_symmetric (qmThetaSymmetric_of_core (qmThetaSymmetricCore_of_linYang hL))

/-- **Route 1, final form: `ThetaPointOfFibre` from `FibreQMPeriod` and `LinYangThetaCurve` (proved).**
Drop-in replacement for `ThetaPt.thetaPointOfFibre_of_qm_ratios hQM hAlg`. -/
theorem thetaPointOfFibre_of_linYang (hQM : FibreQMPeriod) (hL : LinYangThetaCurve) :
    ThetaPointOfFibre :=
  thetaPointOfFibre_of_qm_curve hQM (thetaEightSquare_iff.mp thetaEightSquare)
    (qmThetaSymmetricCurve_of_linYang hL)

end HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal
