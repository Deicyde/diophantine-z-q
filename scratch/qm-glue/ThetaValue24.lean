import Mathlib

/-!
# qm-glue (a): `ThetaQuotientValue24`

The glue `HDec.LeafQCheck.HM.QMSplit.ThetaQuotientValue24` of qm-split (`scratch/qm-split/Haupt.lean`
l.2287), copied verbatim with what it depends on: the definitions of `HDec.PkgI1` (copied verbatim from
`ZInQKernel/OneProof/H/LPrefix.lean` l.221-363, itself from `scratch/pkg-I1/I1.lean`) and `HDec.LeafQCheck.HM.mu`
(qm-split `Haupt.lean` l.1119).

Results (all compiled here):
* `fixedPoint_eq`: the only `τ` fixed by a `γ` with matrix `ι(μ)` is `τ₂₄ = i(√6 + √3) = i√(9 + 6√2)`.
* `omega_tau24`: the period matrix is explicit, `Ω(τ₂₄) = Ω₂₄ := [[(−4+3√−6)/14, (−1−√−6)/7],
  [(−1−√−6)/7, (−4+3√−6)/7]]` (entries in `ℚ(√−6)`).
* `thetaQuotientValue24_iff`: the glue is equivalent to the closed numeric statement
  `ThetaValueAtOmega24`: `jDen Ω₂₄ ≠ 0 ∧ jNum Ω₂₄ / jDen Ω₂₄ = −16/27` (ten theta constants at one explicit
  matrix).
* `thetaQuotientValue24_of_igusa`: the glue from the published value `IgusaCMValue24` (Lin–Yang's weighted
  Igusa vector along the QM curve, eqs. (2), (14), at the Baba–Granath CM value `j = −16/27`), and the
  converse `igusa_of_thetaQuotientValue24` (the leaf has exactly the content of the glue, no more).
-/

set_option linter.all false

open Complex Matrix

noncomputable section

namespace HDec

namespace PkgI1


/-! ## §1 The quaternion datum (N5 L410-420) -/

/-- `B = (2,-3)`: Mathlib's `QuaternionAlgebra R c₁ c₂ c₃` has `i² = c₁ + c₂ i`, `j² = c₃`. -/
abbrev B := QuaternionAlgebra ℚ 2 0 (-3)

/-- `i`, `j`, `k = ij` in `B`. -/
def qi : B := ⟨0, 1, 0, 0⟩
def qj : B := ⟨0, 0, 1, 0⟩
def qk : B := ⟨0, 0, 0, 1⟩

/-- N5's ordered basis `(1, i, (1+j)/2, (i+ij)/2)` of the maximal order `𝒪`. -/
def oBasis : Fin 4 → B := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨1/2, 0, 1/2, 0⟩, ⟨0, 1/2, 0, 1/2⟩]

/-- Membership in `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩`. -/
def InO (x : B) : Prop := ∃ n : Fin 4 → ℤ, x = ∑ k, (n k : ℚ) • oBasis k

/-- `μ = 2j + ij`. -/
def mu : B := ⟨0, 0, 2, 1⟩

/-- `μ⁻¹ = -μ/6`, since `μ² = -6`. -/
def muInv : B := ⟨0, 0, -1/3, -1/6⟩

/-- Reduced trace. -/
def trd (x : B) : ℚ := 2 * x.re

theorem mu_sq : mu * mu = (⟨-6, 0, 0, 0⟩ : B) := by
  ext <;> simp [mu]; norm_num

theorem mu_mul_muInv : mu * muInv = 1 := by
  ext <;> simp [mu, muInv] <;> norm_num

/-- N5's Gram matrix (L413-415). -/
def gram : Matrix (Fin 4) (Fin 4) ℚ := !![0, 0, -1, 1; 0, 0, 1, -2; 1, -1, 0, 0; -1, 2, 0, 0]

/-- **A1 (glue, proved).** `Trd(μ⁻¹ x ȳ)` has N5's Gram matrix in N5's basis. -/
theorem gram_eq (r s : Fin 4) : trd (muInv * oBasis r * star (oBasis s)) = gram r s := by
  fin_cases r <;> fin_cases s <;> simp [trd, muInv, oBasis, gram] <;> norm_num

theorem gram_det : gram.det = 1 := by
  simp [gram, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  rw [show Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 from rfl,
    show Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 from rfl]
  norm_num

/-! ## §2 The real embedding and `Γ*` -/

/-- `ι(i) = [[√2,0],[0,-√2]]`. -/
def Mi : Matrix (Fin 2) (Fin 2) ℝ := !![√2, 0; 0, -√2]
/-- `ι(j) = [[0,-3],[1,0]]`. -/
def Mj : Matrix (Fin 2) (Fin 2) ℝ := !![0, -3; 1, 0]

/-- The real embedding `ι : B → M₂(ℝ)` (a ring homomorphism: `qm_embed.py` checks it on the
basis; `Mi² = 2`, `Mj² = -3`, `Mi Mj = -Mj Mi`). -/
def iota (x : B) : Matrix (Fin 2) (Fin 2) ℝ :=
  (x.re : ℝ) • 1 + (x.imI : ℝ) • Mi + (x.imJ : ℝ) • Mj + (x.imK : ℝ) • (Mi * Mj)

/-- `x ∈ B` is invertible and normalizes `𝒪`. -/
def NormalizesO (x : B) : Prop :=
  ∃ y : B, x * y = 1 ∧ y * x = 1 ∧ ∀ z : B, InO z → InO (x * z * y) ∧ InO (y * z * x)

/-- `Γ* = ι(N_B(𝒪)⁺)` acting on `ℍ`; modulo scalars this is the group of the Atkin–Lehner
quotient `X₆/W` (positive reduced norm = positive determinant). -/
def GammaStar : Set (GL (Fin 2) ℝ) :=
  {γ | ∃ x : B, NormalizesO x ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = iota x ∧
    0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det}

/-! ## §3 Siegel upper half-space and theta constants -/

/-- The Siegel upper half-space of degree 2. -/
def SiegelH2 : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {Ω | Ωᵀ = Ω ∧ (Ω.map Complex.im).PosDef}

/-- A half-integral characteristic `m = (a, b)`, `a b ∈ {0,1}²`. -/
abbrev Char2 := (Fin 2 → Fin 2) × (Fin 2 → Fin 2)

/-- Theta constant `θ_m(Ω) = Σ_{n ∈ ℤ²} exp(πi (n+a/2)ᵀΩ(n+a/2) + πi (n+a/2)ᵀ b)`. -/
def thetaConst (m : Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑' n : Fin 2 → ℤ,
    let v : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2
    Complex.exp (Real.pi * I * (v ⬝ᵥ (Ω *ᵥ v)) + Real.pi * I * (v ⬝ᵥ fun k => ((m.2 k : ℕ) : ℂ)))

/-- The ten even characteristics (`aᵀb ≡ 0 mod 2`). -/
def evenChars : Finset Char2 :=
  Finset.univ.filter fun m => ((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ)) % 2 = 0

theorem card_evenChars : evenChars.card = 10 := by decide

/-- `Σ_{m even} θ_m⁸` (`= 4ψ₄`). -/
def thetaSum8 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := ∑ m ∈ evenChars, thetaConst m Ω ^ 8

/-- `∏_{m even} θ_m²` (`= -2¹⁴χ₁₀`). -/
def thetaProd2 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := ∏ m ∈ evenChars, thetaConst m Ω ^ 2

/-- Numerator of F1: `3779136·(∏θ_m)⁴`. -/
def jNum (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 3779136 * thetaProd2 Ω ^ 2

/-- Denominator of F1: `(Σθ_m⁸)⁵`. -/
def jDen (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := thetaSum8 Ω ^ 5

/-- The action of `Sp₄` on degree-2 matrices: `(AΩ+B)(CΩ+D)⁻¹`. -/
def spAct (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let Mc := M.map (Int.cast : ℤ → ℂ)
  (Mc.toBlocks₁₁ * Ω + Mc.toBlocks₁₂) * (Mc.toBlocks₂₁ * Ω + Mc.toBlocks₂₂)⁻¹

/-- The automorphy factor `det(CΩ+D)`. -/
def spFactor (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    ℂ :=
  let Mc := M.map (Int.cast : ℤ → ℂ)
  (Mc.toBlocks₂₁ * Ω + Mc.toBlocks₂₂).det

/-! ## §4 The modular embedding of N5's QM datum (`qm_embed.py`)

For `τ ∈ ℍ` put `v_τ = (τ, 1)ᵀ` and `Λ_τ = ι(𝒪)v_τ ⊂ ℂ²`, with Riemann form
`E(ι(x)v_τ, ι(y)v_τ) = Trd(μ⁻¹xȳ)`. In N5's basis the Gram matrix is `[[0,P],[-Pᵀ,0]]` with
`P = [[-1,1],[1,-2]]`, `P⁻¹ = [[-2,-1],[-1,-1]]`. So `e = (ι(1)v, ι(i)v)` and
`f' = (ι((1+j)/2)v, ι((i+ij)/2)v)·P⁻¹` is a symplectic basis, and `Ω(τ) = F'(τ)⁻¹E(τ)` is a
period matrix of the principally polarized QM surface `A_τ = ℂ²/Λ_τ` (symmetric with positive
definite imaginary part: VERIFIED numerically; the other normalization `E⁻¹F'` belongs to `-E`). -/

/-- `ι(x)·(τ, 1)ᵀ`. -/
def latVec (x : B) (τ : ℂ) : Fin 2 → ℂ := (iota x).map (fun r : ℝ => (r : ℂ)) *ᵥ ![τ, 1]

/-- `E(τ)`: columns `ι(1)v_τ`, `ι(i)v_τ`. -/
def Emat (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r c => ![latVec (oBasis 0) τ, latVec (oBasis 1) τ] c r

/-- `F₀(τ)`: columns `ι((1+j)/2)v_τ`, `ι((i+ij)/2)v_τ`. -/
def F0mat (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r c => ![latVec (oBasis 2) τ, latVec (oBasis 3) τ] c r

/-- `P⁻¹` for `P = [[-1,1],[1,-2]]`. -/
def Pinv : Matrix (Fin 2) (Fin 2) ℂ := !![-2, -1; -1, -1]

/-- The period matrix `Ω(τ) = (F₀(τ)P⁻¹)⁻¹E(τ)` of the QM surface at `τ`. -/
def Omega (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (F0mat τ * Pinv)⁻¹ * Emat τ

end PkgI1

namespace LeafQCheck.HM

/-- `μ = 2j + ij` (qm-split `Haupt.lean` l.1119, verbatim). -/
def mu : PkgI1.B := ⟨0, 0, 2, 1⟩

namespace QMSplit

open PkgI1

/-- **GLUE (the value of the theta quotient at the CM point of discriminant `−24`).** At the fixed point
`τ = i√(9 + 6√2)` of `ι(μ)`, `μ = 2j + ij`: `jDen(Ω(τ)) ≠ 0` and `jNum(Ω(τ))/jDen(Ω(τ)) = −16/27`.
Numerically VERIFIED by leaf-review-a (`py/hauptmodul_check.py`: `−0.592592592592593`). Sources for a proof:
Baba–Granath, Canad. J. Math. 60 (2008) (Igusa invariants of the QM family as functions of the Hauptmodul of
`X₆/W`, and its CM values) with Igusa's theta expressions of the Igusa invariants (Amer. J. Math. 89 (1967));
locators UNVERIFIED. -/
def ThetaQuotientValue24 : Prop :=
  ∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu → ∀ τ : UpperHalfPlane, γ • τ = τ →
    PkgI1.jDen (PkgI1.Omega τ) ≠ 0 ∧
      PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = -16 / 27

end QMSplit
end LeafQCheck.HM
end HDec

/-! ## Proofs -/

namespace HDec.LeafQCheck.HM.QMSplit.Value24

open PkgI1 UpperHalfPlane

theorem iota_mu : PkgI1.iota mu = !![0, -6 - 3 * √2; 2 - √2, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [PkgI1.iota, mu, PkgI1.Mi, PkgI1.Mj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem sqrt2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
theorem sqrt3_sq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
theorem sqrt6_eq : (√6 : ℝ) = √2 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
theorem sqrt2_lt : (√2 : ℝ) < 2 := by
  rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- `s₂₄ = √6 + √3`, so `τ₂₄ = i s₂₄` and `s₂₄² = 9 + 6√2`. -/
def s24 : ℝ := √6 + √3

theorem s24_pos : 0 < s24 := by unfold s24; positivity

theorem s24_sq : s24 ^ 2 = 9 + 6 * √2 := by
  unfold s24; rw [sqrt6_eq]
  have h2 := sqrt2_sq; have h3 := sqrt3_sq
  linear_combination (√3 ^ 2) * h2 + (3 + 2 * √2) * h3

/-- From qm-split `Haupt.lean` l.652 (`fixed_data`, verbatim): the fixed-point equations. -/
theorem fixed_data {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) :
    (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
        2 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re + (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
        -(γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (P.re ^ 2 + P.im ^ 2) := by
  have hd' : 0 < γ.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  have h := congrArg (fun w : UpperHalfPlane => (w : ℂ)) hP
  rw [UpperHalfPlane.coe_smul_of_det_pos hd', div_eq_iff (denom_ne_zero γ P)] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [UpperHalfPlane.num, UpperHalfPlane.denom] at hre him
  have hq := P.im_pos
  have ha : ((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - 2 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re -
      (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1) * P.im = 0 := by linear_combination him
  have ha' := (mul_eq_zero.1 ha).resolve_right hq.ne'
  refine ⟨by linarith, ?_⟩
  have : (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
      2 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re + (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    linarith
  rw [this] at hre
  linear_combination hre

/-- **The CM point.** The only point fixed by a `γ` with matrix `ι(μ)` is `τ₂₄ = i(√6 + √3)`. -/
theorem fixedPoint_eq (γ : GL (Fin 2) ℝ) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu)
    (τ : UpperHalfPlane) (h : γ • τ = τ) : (τ : ℂ) = Complex.I * (s24 : ℂ) := by
  have h2 := sqrt2_lt
  have hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [hγ, iota_mu, Matrix.det_fin_two_of]; nlinarith [sqrt2_sq]
  obtain ⟨e1, e2⟩ := fixed_data hd h
  rw [hγ, iota_mu] at e1 e2
  simp at e1 e2
  have hc : (2 - √2 : ℝ) ≠ 0 := by linarith
  have hre : τ.re = 0 := e1.resolve_left hc
  rw [hre] at e2
  have him2 : τ.im ^ 2 = s24 ^ 2 := by
    rw [s24_sq]
    have : (2 - √2) * (τ.im ^ 2 - (9 + 6 * √2)) = 0 := by
      linear_combination e2 + 6 * sqrt2_sq
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hc
    · linarith
  have him : τ.im = s24 := by
    have := τ.im_pos; have := s24_pos
    nlinarith [sq_nonneg (τ.im - s24), sq_nonneg (τ.im + s24)]
  apply Complex.ext <;> simp [hre, him]

/-- The explicit period matrix at `τ₂₄` (entries in `ℚ(√−6)`). -/
def Om24 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(-4 + 3 * Complex.I * ((√6 : ℝ) : ℂ)) / 14, (-1 - Complex.I * ((√6 : ℝ) : ℂ)) / 7;
     (-1 - Complex.I * ((√6 : ℝ) : ℂ)) / 7, (-4 + 3 * Complex.I * ((√6 : ℝ) : ℂ)) / 7]

theorem Emat_eq (τ : ℂ) : PkgI1.Emat τ = !![τ, (√2 : ℂ) * τ; 1, -(√2 : ℂ)] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [PkgI1.Emat, PkgI1.latVec, PkgI1.iota, PkgI1.oBasis, PkgI1.Mi, PkgI1.Mj, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.mul_apply]

theorem F0mat_eq (τ : ℂ) : PkgI1.F0mat τ =
    !![(τ - 3) / 2, (√2 : ℂ) * (τ - 3) / 2; (τ + 1) / 2, -(√2 : ℂ) * (τ + 1) / 2] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [PkgI1.F0mat, PkgI1.latVec, PkgI1.iota, PkgI1.oBasis, PkgI1.Mi, PkgI1.Mj, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.mul_apply] <;> ring

theorem c2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast sqrt2_sq
theorem c3 : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast sqrt3_sq

/-- **The period matrix at `τ₂₄`**: `Ω(τ₂₄) = Ω₂₄`. -/
theorem omega_tau24 : PkgI1.Omega (Complex.I * (s24 : ℂ)) = Om24 := by
  set τ : ℂ := Complex.I * (s24 : ℂ) with hτ
  have ha := c2; have hb := c3
  have ha3 : ((√2 : ℝ) : ℂ) ^ 3 = 2 * ((√2 : ℝ) : ℂ) := by rw [pow_succ, ha]
  have hb3 : ((√3 : ℝ) : ℂ) ^ 3 = 3 * ((√3 : ℝ) : ℂ) := by rw [pow_succ, hb]
  have hA : (PkgI1.F0mat τ * PkgI1.Pinv) * Om24 = PkgI1.Emat τ := by
    rw [F0mat_eq, Emat_eq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Om24, PkgI1.Pinv, Matrix.mul_apply, Fin.sum_univ_two, hτ, s24, sqrt6_eq] <;>
      ring_nf <;> simp only [ha, hb, ha3, hb3, Complex.I_sq] <;> ring_nf
  have him : τ.im ≠ 0 := by simp [hτ]; exact s24_pos.ne'
  have h1 : τ - 3 ≠ 0 := fun h => him (by simpa using congrArg Complex.im h)
  have h2 : τ + 1 ≠ 0 := fun h => him (by simpa using congrArg Complex.im h)
  have hdet : IsUnit (PkgI1.F0mat τ * PkgI1.Pinv).det := by
    rw [Matrix.det_mul, F0mat_eq, Matrix.det_fin_two_of]
    have hP : PkgI1.Pinv.det = 1 := by simp [PkgI1.Pinv, Matrix.det_fin_two_of]; norm_num
    rw [hP, mul_one, isUnit_iff_ne_zero]
    have : (τ - 3) / 2 * (-((√2 : ℝ) : ℂ) * (τ + 1) / 2) - ((√2 : ℝ) : ℂ) * (τ - 3) / 2 * ((τ + 1) / 2)
        = -(((√2 : ℝ) : ℂ) * (τ - 3) * (τ + 1)) / 2 := by ring
    rw [this]
    have : ((√2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'
    simp [h1, h2, this]
  unfold PkgI1.Omega
  rw [← hA, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

/-! ## The glue as a closed numeric statement -/

/-- **The glue at the explicit period matrix**: the ten even theta constants at `Ω₂₄` satisfy
`(Σθ⁸)⁵ ≠ 0` and `3779136(∏θ²)²/(Σθ⁸)⁵ = −16/27`. -/
def ThetaValueAtOmega24 : Prop :=
  PkgI1.jDen Om24 ≠ 0 ∧ PkgI1.jNum Om24 / PkgI1.jDen Om24 = -16 / 27

theorem det_iota_mu : (PkgI1.iota mu).det = 6 := by
  rw [iota_mu, Matrix.det_fin_two_of]; linear_combination (-3 : ℝ) * sqrt2_sq

/-- `γ_μ ∈ GL₂(ℝ)` with matrix `ι(μ)`. -/
def gammaMu : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (PkgI1.iota mu) (by rw [det_iota_mu]; norm_num)

/-- `τ₂₄ ∈ ℍ`. -/
def tau24 : UpperHalfPlane := ⟨Complex.I * (s24 : ℂ), by simpa using s24_pos⟩

theorem gammaMu_fix : gammaMu • tau24 = tau24 := by
  have hd : 0 < gammaMu.det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    show 0 < (PkgI1.iota mu).det
    rw [det_iota_mu]; norm_num
  have hc : ((2 : ℂ) - ((√2 : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have : (√2 : ℝ) = 2 := by exact_mod_cast (sub_eq_zero.1 h).symm
    linarith [sqrt2_lt]
  have hs : ((s24 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast s24_pos.ne'
  have hs2 : ((s24 : ℝ) : ℂ) ^ 2 = 9 + 6 * ((√2 : ℝ) : ℂ) := by exact_mod_cast s24_sq
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hd, div_eq_iff (UpperHalfPlane.denom_ne_zero _ _)]
  have hval : (gammaMu : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu := rfl
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hval, iota_mu, tau24, UpperHalfPlane.coe_mk]
  simp
  linear_combination (-(2 - ((√2 : ℝ) : ℂ)) * ((s24 : ℝ) : ℂ) ^ 2) * Complex.I_sq +
    (2 - ((√2 : ℝ) : ℂ)) * hs2 + (-6 : ℂ) * c2

/-- **(a), exact part.** The glue `ThetaQuotientValue24` is equivalent to the closed statement
`ThetaValueAtOmega24` about the theta constants at the explicit matrix `Ω₂₄`. -/
theorem thetaQuotientValue24_iff : ThetaQuotientValue24 ↔ ThetaValueAtOmega24 := by
  constructor
  · intro h
    have := h gammaMu rfl tau24 gammaMu_fix
    have e : ((tau24 : UpperHalfPlane) : ℂ) = Complex.I * (s24 : ℂ) := rfl
    rw [e, omega_tau24] at this
    exact this
  · intro h γ hγ τ hτ
    rw [fixedPoint_eq γ hγ τ hτ, omega_tau24]
    exact h

/-! ## Reduction to the published value -/

/-- Verbatim from `ZInQKernel/OneProof/H/LPrefix.lean` §7 (`HDec.PkgI1.f1_algebra`). -/
theorem f1_algebra {K : Type*} [Field K] [CharZero K] (j lam J2 J4 J10 Sig Pi : K)
    (hJ2 : J2 = 12 * (j + 1) * lam) (hJ4 : J4 = 6 * (j ^ 2 + j + 1) * lam ^ 2)
    (hJ10 : J10 = j ^ 3 * lam ^ 5)
    (hpsi : J2 ^ 2 - 24 * J4 = Sig / 4) (hchi : -J10 / 4 = -Pi / 2 ^ 14) :
    j * Sig ^ 5 = 3779136 * Pi ^ 2 := by
  have hS : Sig = 576 * j * lam ^ 2 := by
    rw [hJ2, hJ4] at hpsi; linear_combination (-4 : K) * hpsi
  have hP : Pi = 4096 * j ^ 3 * lam ^ 5 := by
    rw [hJ10] at hchi; linear_combination (16384 : K) * hchi
  rw [hS, hP]; ring

/-- **LEAF (published value: the Igusa invariants at the CM point of discriminant `−24`).** At the fixed
point `τ` of `ι(μ)` (the CM point of discriminant `−24` of `X₆/W` in the modular embedding of `PkgI1` §4,
whose Riemann form is Lin–Yang's convention, eq. (3) and Lemma 3), Igusa's invariants of the principally
polarized surface with period matrix `Ω(τ)` are, in a weighted representative, Lin–Yang's vector
`J₂ = 12(j+1)λ`, `J₄ = 6(j²+j+1)λ²`, `J₁₀ = j³λ⁵` at `j = −16/27`, with Igusa's
`ψ₄ = J₂² − 24J₄`, `χ₁₀ = −J₁₀/4` and LNY's theta conventions `ψ₄ = Σθ_m⁸/4`, `χ₁₀ = −∏θ_m²/2¹⁴`.

Published form: Lin–Yang, *Quaternionic loci in Siegel's modular threefold* (Math. Z., 2020; arXiv v1),
eqs. (2) and (14), pp. 3 and 17 (the Igusa vector of the QM curve of discriminant 6 as a function of the
Hauptmodul `j` of `X₆/W`), with the CM value `j = −16/27` at discriminant `−24` (Baba–Granath, Canad. J. Math.
60 (2008), Thm 2.1 and the CM table; Elkies, ANTS-III (1998), the CM points of `X*(6)`); Lauter–Naehrig–Yang
(2015) §2.2, p. 4 for the theta conventions; Igusa, Amer. J. Math. 89 (1967). This is the citation of the
manuscript, l.908-923 (`diophantine_zq.tex`). Locators UNVERIFIED (no network); the manuscript cites
exactly these equations and pages.

Content: by `igusa_of_thetaQuotientValue24` this leaf is *equivalent* to the glue `ThetaQuotientValue24`
(it restates it in Igusa's normalization; it is not stronger). The published content that it uses is one
number: the value of Lin–Yang's normalized Hauptmodul at the discriminant `−24` point. -/
def IgusaCMValue24 : Prop :=
  ∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu → ∀ τ : UpperHalfPlane, γ • τ = τ →
    ∃ lam J2 J4 J10 : ℂ, lam ≠ 0 ∧
      J2 = 12 * ((-16 / 27 : ℂ) + 1) * lam ∧
      J4 = 6 * ((-16 / 27 : ℂ) ^ 2 + (-16 / 27 : ℂ) + 1) * lam ^ 2 ∧
      J10 = (-16 / 27 : ℂ) ^ 3 * lam ^ 5 ∧
      J2 ^ 2 - 24 * J4 = PkgI1.thetaSum8 (PkgI1.Omega τ) / 4 ∧
      -J10 / 4 = -PkgI1.thetaProd2 (PkgI1.Omega τ) / 2 ^ 14

/-- **(a): the glue from the published value.** -/
theorem thetaQuotientValue24_of_igusa (h : IgusaCMValue24) : ThetaQuotientValue24 := by
  intro γ hγ τ hτ
  obtain ⟨lam, J2, J4, J10, hlam, h2, h4, h10, hpsi, hchi⟩ := h γ hγ τ hτ
  have key := f1_algebra (-16 / 27 : ℂ) lam J2 J4 J10 _ _ h2 h4 h10 hpsi hchi
  have hS : PkgI1.thetaSum8 (PkgI1.Omega τ) = 576 * (-16 / 27) * lam ^ 2 := by
    rw [h2, h4] at hpsi; linear_combination (-4 : ℂ) * hpsi
  have hS0 : PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 := by
    rw [hS]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hlam)
  have hD : PkgI1.jDen (PkgI1.Omega τ) ≠ 0 := pow_ne_zero _ hS0
  refine ⟨hD, ?_⟩
  rw [div_eq_iff hD]
  simp only [PkgI1.jNum, PkgI1.jDen]
  linear_combination -key

/-- **The converse: the leaf is not stronger than the glue.** -/
theorem igusa_of_thetaQuotientValue24 (h : ThetaQuotientValue24) : IgusaCMValue24 := by
  intro γ hγ τ hτ
  obtain ⟨hD, hv⟩ := h γ hγ τ hτ
  set Sig := PkgI1.thetaSum8 (PkgI1.Omega τ)
  set Pi := PkgI1.thetaProd2 (PkgI1.Omega τ)
  have hS0 : Sig ≠ 0 := fun h0 => hD (by simp [PkgI1.jDen, Sig, h0])
  have key : 3779136 * Pi ^ 2 = (-16 / 27) * Sig ^ 5 := by
    rw [div_eq_iff hD] at hv; simpa [PkgI1.jNum, PkgI1.jDen] using hv
  obtain ⟨l0, hl0⟩ := IsAlgClosed.exists_pow_nat_eq (Sig / (576 * (-16 / 27))) (n := 2) (by norm_num)
  have hl0' : Sig = 576 * (-16 / 27) * l0 ^ 2 := by rw [hl0]; field_simp
  have hl00 : l0 ≠ 0 := by rintro rfl; simp at hl0'; exact hS0 hl0'
  -- `Pi² = (4096 j³ l0⁵)²`, so `Pi = ± 4096 j³ l0⁵`
  have hsq : (Pi - 4096 * (-16 / 27) ^ 3 * l0 ^ 5) * (Pi + 4096 * (-16 / 27) ^ 3 * l0 ^ 5) = 0 := by
    rw [hl0'] at key; linear_combination key / 3779136
  have hsign : ∃ lam : ℂ, lam ≠ 0 ∧ Sig = 576 * (-16 / 27) * lam ^ 2 ∧
      Pi = 4096 * (-16 / 27) ^ 3 * lam ^ 5 := by
    rcases mul_eq_zero.1 hsq with e | e
    · exact ⟨l0, hl00, hl0', by linear_combination e⟩
    · exact ⟨-l0, neg_ne_zero.2 hl00, by rw [hl0']; ring, by linear_combination e⟩
  obtain ⟨lam, hlam, hS, hP⟩ := hsign
  refine ⟨lam, _, _, _, hlam, rfl, rfl, rfl, ?_, ?_⟩
  · rw [hS]; ring
  · rw [hP]; ring

end HDec.LeafQCheck.HM.QMSplit.Value24

#print axioms HDec.LeafQCheck.HM.QMSplit.Value24.thetaQuotientValue24_iff
#print axioms HDec.LeafQCheck.HM.QMSplit.Value24.thetaQuotientValue24_of_igusa
#print axioms HDec.LeafQCheck.HM.QMSplit.Value24.igusa_of_thetaQuotientValue24
