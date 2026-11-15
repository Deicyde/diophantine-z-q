import ZInQKernel.Contrib.OneProof.LinYangGlue

/-! # theta-fold (4/4): the printed leaves `IgusaThetaExpressions`, `LinYangEx29All` and Route 1 from them

linyang-printed's scratch/linyang-printed/LinYangPrintedFull.lean §1-§4 and §10: the genuine Siegel Eisenstein
series `siegelEis k` (a sum over `Γ_∞\Sp₄(ℤ)`), Igusa's `χ₁₀`, `χ₁₂` (1962 combinations), Lin–Yang's `s_k`; the
two LEAVES `IgusaThetaExpressions` (Igusa 1964/1967) and `LinYangEx29All` (Lin–Yang 2020, Example 29, the
relations only); `LinYangThetaCurve` from them (eliminating `j₆`, density off one countable `Γ*`-orbit); and
`thetaRatiosAtQM_of_printedAll`, which the chain's top `HDec.HSyn.sixContactMin_of_open29` uses in place of the
field `thetaRatiosAlgebraic`. Locators of both leaves UNVERIFIED (see the docstrings).
docs/research/theta-fold.md, docs/research/linyang-printed.md. -/

noncomputable section

namespace HDec.HSyn.G0Split.ThetaPt.LinYangPrinted

open Complex Matrix Filter Topology
open ThetaGlue (psi4Th psi6Th chi10Th chi12Th LinYangThetaCurve)
open HSyn.G0Split.FibreQM.PeriodMap (U isOpen_U thTerm qf quad_lower differentiableAt_omega summable_gb2
  norm_thTerm_le omegaSiegel_proof)

/-! ## 1. Genuine definitions: Siegel Eisenstein series, Igusa's `χ₁₀`, `χ₁₂`, Lin–Yang's `s_k` -/

/-- Integer `4 × 4` matrices in block form. -/
abbrev SpMat := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ

/-- Same coset of the Siegel parabolic `Γ_∞ = {M ∈ Sp₄(ℤ) : C = 0}`: the bottom block rows satisfy
`(C_N, D_N) = U·(C_M, D_M)` for some `U ∈ GL₂(ℤ)`. -/
def botRel (M N : Matrix.symplecticGroup (Fin 2) ℤ) : Prop :=
  ∃ U : GL (Fin 2) ℤ,
    (N : SpMat).toBlocks₂₁ = (U : Matrix (Fin 2) (Fin 2) ℤ) * (M : SpMat).toBlocks₂₁ ∧
    (N : SpMat).toBlocks₂₂ = (U : Matrix (Fin 2) (Fin 2) ℤ) * (M : SpMat).toBlocks₂₂

theorem botRel_equiv : Equivalence botRel where
  refl M := ⟨1, by simp, by simp⟩
  symm := by
    rintro M N ⟨U, h1, h2⟩
    refine ⟨U⁻¹, ?_, ?_⟩
    · rw [h1, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    · rw [h2, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  trans := by
    rintro M N P ⟨U, h1, h2⟩ ⟨V, h3, h4⟩
    refine ⟨V * U, ?_, ?_⟩
    · rw [h3, h1, Units.val_mul, Matrix.mul_assoc]
    · rw [h4, h2, Units.val_mul, Matrix.mul_assoc]

/-- The coset relation as a setoid on `Sp₄(ℤ)`. -/
def botSetoid : Setoid (Matrix.symplecticGroup (Fin 2) ℤ) := ⟨botRel, botRel_equiv⟩

/-- `Γ_∞\Sp₄(ℤ)`, i.e. the classes of coprime symmetric pairs `(C, D)` modulo `GL₂(ℤ)`. -/
abbrev SiegelCosets := Quotient botSetoid

/-- **The Siegel Eisenstein series of degree 2 and weight `k`** (Igusa, Amer. J. Math. 84 (1962), the forms
`ψ_k`; the standard definition, e.g. Klingen, *Introductory lectures on Siegel modular forms*, §5):
`ψ_k(Ω) = Σ_{M ∈ Γ_∞\Sp₄(ℤ)} det(CΩ + D)^{-k}`, one representative per coset. For even `k` the summand does not
depend on the representative (`det U = ±1`); for `k ≥ 4` the series converges absolutely on `𝔥₂`, so the `tsum`
is the classical value. -/
def siegelEis (k : ℕ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑' c : SiegelCosets,
    (PkgI1.spFactor ((Quotient.out c : Matrix.symplecticGroup (Fin 2) ℤ) : SpMat) Ω)⁻¹ ^ k

/-- **Igusa's cusp form `χ₁₀`** (Igusa 1962, as a combination of Eisenstein series; constants recalled,
UNVERIFIED as a citation, VERIFIED against the theta expression on 76 Fourier coefficients, py/fourier.py):
`χ₁₀ = −43867·2⁻¹²3⁻⁵5⁻²7⁻¹53⁻¹ (ψ₄ψ₆ − ψ₁₀)`. -/
def igusaChi10E (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (-43867 / (2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 * 53) : ℂ) * (siegelEis 4 Ω * siegelEis 6 Ω - siegelEis 10 Ω)

/-- **Igusa's cusp form `χ₁₂`** (Igusa 1962; same status as `igusaChi10E`):
`χ₁₂ = 131·593·2⁻¹³3⁻⁷5⁻³7⁻²337⁻¹ (3²7²ψ₄³ + 2·5³ψ₆² − 691ψ₁₂)`. -/
def igusaChi12E (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (131 * 593 / (2 ^ 13 * 3 ^ 7 * 5 ^ 3 * 7 ^ 2 * 337) : ℂ) *
    (3 ^ 2 * 7 ^ 2 * siegelEis 4 Ω ^ 3 + 2 * 5 ^ 3 * siegelEis 6 Ω ^ 2 - 691 * siegelEis 12 Ω)

/-- Lin–Yang's normalized generators (arXiv:1807.00466v1 §2, as restated in scratch/h-v14/igusa_check.py):
`s₂ = ψ₄`. -/
def lyS2 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := siegelEis 4 Ω
/-- `s₃ = ψ₆`. -/
def lyS3 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := siegelEis 6 Ω
/-- `s₅ = 2¹²3⁵χ₁₀`. -/
def lyS5 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 2 ^ 12 * 3 ^ 5 * igusaChi10E Ω
/-- `s₆ = 2¹²3⁶χ₁₂`. -/
def lyS6 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 2 ^ 12 * 3 ^ 6 * igusaChi12E Ω

/-! ## 2. The two leaves, in printed form -/

/-- **LEAF (Igusa: the theta expressions of the generators).** On the Siegel upper half-space `𝔥₂`, the Eisenstein
series `ψ₄`, `ψ₆` and Igusa's cusp forms `χ₁₀`, `χ₁₂` equal their theta expressions:
`ψ₄ = 2⁻² Σ_m θ_m⁸`, `ψ₆ = 2⁻² Σ_{syzygous} ±(θ_{m₁}θ_{m₂}θ_{m₃})⁴`, `χ₁₀ = −2⁻¹⁴ ∏_m θ_m²`,
`χ₁₂ = 2⁻¹⁷3⁻¹ Σ_{Göpel Q} ∏_{m ∉ Q} θ_m⁴` (theta-glue's `psi4Th`, `psi6Th`, `chi10Th`, `chi12Th`).

Sources: J.-I. Igusa, *On Siegel modular forms of genus two (II)*, Amer. J. Math. 86 (1964), and *Modular forms and
projective invariants*, Amer. J. Math. 89 (1967), p. 848 (locators UNVERIFIED, no network; the printed sign rule of
`ψ₆` was not read). Evidence (VERIFIED, exact, py/fourier.py): all 76 Fourier coefficients at half-integral
`T = (n, r, m)`, `n, m ≤ 2`, agree on both sides; since `dim M_k(Sp₄(ℤ)) = 1, 1, 2, 3` for `k = 4, 6, 10, 12` and
the theta expressions are modular (theta-glue py/invariants.py), this pins the identities, including the sign
choice in `ψ₆` and Igusa's 1962 constants in `igusaChi10E`, `igusaChi12E`. Form: printed (the theta expressions as
theorems about Igusa's forms). -/
def IgusaThetaExpressions : Prop :=
  ∀ Ω ∈ PkgI1.SiegelH2,
    siegelEis 4 Ω = psi4Th Ω ∧ siegelEis 6 Ω = psi6Th Ω ∧
      igusaChi10E Ω = chi10Th Ω ∧ igusaChi12E Ω = chi12Th Ω

/-- **LEAF (Lin–Yang 2020, Example 29: the quaternionic locus of discriminant 6 in Igusa's generators, as functions
of the Hauptmodul `j₆`).** There is a Hauptmodul `j₆ : Γ*\ℍ = X₆/W → P¹` (continuous on `ℍ`, fibres exactly the
`Γ*`-orbits, surjective) with `j₆ = 0, ∞, −16/27` at the CM points of discriminants `−4, −3, −24`, such that along the
modular embedding `τ ↦ Ω(τ)` of the QM surfaces, wherever `j₆(τ) = z ≠ ∞`,
`s₃² = z·s₂³`, `s₅ = s₂s₃`, `s₆ = (z + 1)·s₂³`,
i.e. Lin–Yang's printed `s₃²/s₂³ = j₆`, `s₅/(s₂s₃) = 1`, `s₆/s₂³ = j₆ + 1` with denominators cleared.

Sources: Y.-H. Lin, Y. Yang, *Quaternionic loci in Siegel's modular threefold*, Math. Z. 295 (2020), 775-819;
arXiv:1807.00466v1, Example 29 (pp. 20-21, discriminant 6; the Hauptmodul `j₆` of `X₀⁶(1)/W₆` defined by its values
at the CM points of discriminants `−4, −3, −24`, VERIFIED in arXiv v1 by h-v14 row L719), with the normalization
`s₂ = ψ₄, s₃ = ψ₆, s₅ = 2¹²3⁵χ₁₀, s₆ = 2¹²3⁶χ₁₂` and the constants `c₁ = c₂ = c₃ = c₄ = 1` (h-v14 §5.3,
scratch/h-v14/igusa_check.py, from the arXiv text: Lin–Yang fix them at discriminant `−19`, `j₆ = 81/64`; the
display itself was not re-read here: UNVERIFIED). Form: consequence of the printed statement (an identity of
meromorphic functions on `X₆/W`, evaluated where `j₆` is finite), never stronger. Faithfulness: as for
`PkgI1.QMHauptmodul`, `Ω(τ)` is pkg-I1's period matrix of the principally polarized QM surface at `τ` (pkg-I1 §4);
the ratios are `Sp₄(ℤ)`-invariant, so the choice of symplectic basis does not matter. The CM clauses are verbatim
those of `PkgI1.QMHauptmodul`. Numerically consistent: with Igusa's theta expressions this is theta-glue's
80-digit check of `LinYangThetaCurve` together with pkg-I1's values of `j_θ = s₃²/s₂³ ∘ Ω`. -/
def LinYangEx29 : Prop :=
  ∃ j6 : UpperHalfPlane → OnePoint ℂ, Continuous j6 ∧
    (∀ τ τ' : UpperHalfPlane, j6 τ = j6 τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ') ∧
    Function.Surjective j6 ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -1 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = ((0 : ℂ) : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x - x + 1 = 0 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -6 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = ((-16/27 : ℂ) : OnePoint ℂ)) ∧
    ∀ τ : UpperHalfPlane, ∀ z : ℂ, j6 τ = (z : OnePoint ℂ) →
      lyS3 (PkgI1.Omega τ) ^ 2 = z * lyS2 (PkgI1.Omega τ) ^ 3 ∧
      lyS5 (PkgI1.Omega τ) = lyS2 (PkgI1.Omega τ) * lyS3 (PkgI1.Omega τ) ∧
      lyS6 (PkgI1.Omega τ) = (z + 1) * lyS2 (PkgI1.Omega τ) ^ 3

/-! ## 3. Glue (proved): continuity along `Ω(τ)`, countable orbits, density -/

/-- Each theta constant along `Ω` is analytic on `ℍ` (copy of the inner step of period-map's
`thetaOmegaAnalytic_of`, TailJ). -/
theorem thetaConst_omega_analyticAt {τ₀ : ℂ} (hτ₀ : τ₀ ∈ U) (m : PkgI1.Char2) :
    AnalyticAt ℂ (fun τ => PkgI1.thetaConst m (PkgI1.Omega τ)) τ₀ := by
  have hS := omegaSiegel_proof
  have hτ₀' : (0 : ℝ) < τ₀.im := hτ₀
  obtain ⟨hsym, hpd⟩ := hS τ₀ hτ₀'
  set p : ℂ → ℝ := fun τ => (PkgI1.Omega τ 0 0).im with hp
  set q : ℂ → ℝ := fun τ => ((PkgI1.Omega τ 0 1).im + (PkgI1.Omega τ 1 0).im) / 2 with hq
  set r : ℂ → ℝ := fun τ => (PkgI1.Omega τ 1 1).im with hr
  have hcont : ∀ i j, ContinuousAt (fun τ => (PkgI1.Omega τ i j).im) τ₀ := fun i j =>
    Complex.continuous_im.continuousAt.comp (differentiableAt_omega hτ₀'.ne' i j).continuousAt
  have hp0 : 0 < p τ₀ := by
    have := hpd.diag_pos (i := 0); simpa [hp] using this
  have hr0 : 0 < r τ₀ := by
    have := hpd.diag_pos (i := 1); simpa [hr] using this
  have hsym01 : PkgI1.Omega τ₀ 1 0 = PkgI1.Omega τ₀ 0 1 := by
    have := congrFun (congrFun hsym 0) 1; simpa using this
  have hdet0 : 0 < p τ₀ * r τ₀ - q τ₀ ^ 2 := by
    have := hpd.det_pos
    rw [Matrix.det_fin_two] at this
    simp only [Matrix.map_apply] at this
    rw [hsym01] at this
    simp only [hp, hq, hr, hsym01]
    nlinarith [this]
  set g : ℂ → ℝ := fun τ => (p τ * r τ - q τ ^ 2) / (p τ + r τ) with hg
  have hg0 : 0 < g τ₀ := div_pos hdet0 (add_pos hp0 hr0)
  have hpc : ContinuousAt p τ₀ := hcont 0 0
  have hrc : ContinuousAt r τ₀ := hcont 1 1
  have hqc : ContinuousAt q τ₀ := ((hcont 0 1).add (hcont 1 0)).div_const 2
  have hgc : ContinuousAt g τ₀ :=
    ((hpc.mul hrc).sub (hqc.pow 2)).div (hpc.add hrc) (add_pos hp0 hr0).ne'
  have hev : ∀ᶠ τ in 𝓝 τ₀, τ ∈ U ∧ 0 < p τ + r τ ∧ g τ₀ / 2 < g τ := by
    refine (show ∀ᶠ τ in 𝓝 τ₀, τ ∈ U from isOpen_U.mem_nhds hτ₀).and ((?_ : ∀ᶠ τ in 𝓝 τ₀, 0 < p τ + r τ).and ?_)
    · exact (hpc.add hrc).eventually (lt_mem_nhds (add_pos hp0 hr0))
    · exact hgc.eventually (lt_mem_nhds (half_lt_self hg0))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set c := g τ₀ / 2 with hcdef
  have hc : 0 < c := half_pos hg0
  have hq_ball : ∀ τ ∈ Metric.ball τ₀ ε, ∀ w : Fin 2 → ℝ, c * (w 0 ^ 2 + w 1 ^ 2) ≤ qf τ w := by
    intro τ hτ w
    obtain ⟨-, hpr, hgt⟩ := hball τ hτ
    have hl := quad_lower (p τ) (q τ) (r τ) (w 0) (w 1) hpr
    have hw : 0 ≤ w 0 ^ 2 + w 1 ^ 2 := by positivity
    calc c * (w 0 ^ 2 + w 1 ^ 2) ≤ g τ * (w 0 ^ 2 + w 1 ^ 2) :=
          mul_le_mul_of_nonneg_right hgt.le hw
      _ ≤ _ := by
        refine hl.trans (le_of_eq ?_)
        simp only [qf, hp, hq, hr]
        ring
  have hdiff : ∀ n, DifferentiableOn ℂ (thTerm m n) (Metric.ball τ₀ ε) := by
    intro n σ hσ
    have hσU : (0 : ℝ) < σ.im := (hball σ hσ).1
    have hΩ := fun i j => differentiableAt_omega hσU.ne' i j
    apply DifferentiableAt.differentiableWithinAt
    set V : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2 with hV
    set Bv : Fin 2 → ℂ := fun k => ((m.2 k : ℕ) : ℂ) with hBv
    have key : thTerm m n = fun τ => Complex.exp (Real.pi * I * (V ⬝ᵥ (PkgI1.Omega τ *ᵥ V)) +
        Real.pi * I * (V ⬝ᵥ Bv)) := rfl
    have hq : DifferentiableAt ℂ (fun τ => V ⬝ᵥ (PkgI1.Omega τ *ᵥ V)) σ := by
      simp only [dotProduct, Matrix.mulVec]
      refine DifferentiableAt.fun_sum fun i _ => ?_
      refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun j _ => ?_) _
      exact (hΩ i j).mul_const _
    rw [key]
    exact ((hq.const_mul _).add_const _).cexp
  have hdon : DifferentiableOn ℂ (fun τ => PkgI1.thetaConst m (PkgI1.Omega τ))
      (Metric.ball τ₀ ε) :=
    differentiableOn_tsum_of_summable_norm (summable_gb2 hc) hdiff Metric.isOpen_ball
      (fun n τ hτ => norm_thTerm_le hc m n τ (hq_ball τ hτ))
  exact hdon.analyticAt (Metric.ball_mem_nhds τ₀ hε)

/-- The ten theta constants along `Ω` are continuous on `ℍ`. -/
theorem thetaVec_continuousOn :
    ContinuousOn (fun τ : ℂ => fun m : PkgI1.Char2 => PkgI1.thetaConst m (PkgI1.Omega τ)) U :=
  continuousOn_pi.mpr fun m _ hτ => (thetaConst_omega_analyticAt hτ m).continuousAt.continuousWithinAt

/-- `ψ₄` as a polynomial in the theta constants. -/
def Q4 (t : PkgI1.Char2 → ℂ) : ℂ := (∑ m ∈ PkgI1.evenChars, t m ^ 8) / 4
/-- `χ₁₀` as a polynomial in the theta constants. -/
def Q10 (t : PkgI1.Char2 → ℂ) : ℂ := -(∏ m ∈ PkgI1.evenChars, t m ^ 2) / 2 ^ 14
def Q6 (t : PkgI1.Char2 → ℂ) : ℂ :=
  (1 / 4) * ((t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 0])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 1]) * t (![1, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 1]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0])) ^ 4
     + (t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 1])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 4
     + (t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 4)

def Q12 (t : PkgI1.Char2 → ℂ) : ℂ :=
  (1 / (2 ^ 17 * 3)) * ((t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4)

theorem psi4Th_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) : psi4Th Ω = Q4 (fun m => PkgI1.thetaConst m Ω) := rfl
set_option maxRecDepth 100000 in
theorem psi6Th_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) : psi6Th Ω = Q6 (fun m => PkgI1.thetaConst m Ω) := rfl
theorem chi10Th_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) : chi10Th Ω = Q10 (fun m => PkgI1.thetaConst m Ω) := rfl
set_option maxRecDepth 100000 in
theorem chi12Th_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) : chi12Th Ω = Q12 (fun m => PkgI1.thetaConst m Ω) := rfl

theorem continuous_Q4 : Continuous Q4 :=
  (continuous_finset_sum _ fun m _ => (continuous_apply m).pow 8).div_const 4
theorem continuous_Q10 : Continuous Q10 :=
  (continuous_finset_prod _ fun m _ => (continuous_apply m).pow 2).neg.div_const _
theorem continuous_Q6 : Continuous Q6 := by unfold Q6; fun_prop
theorem continuous_Q12 : Continuous Q12 := by unfold Q12; fun_prop

theorem contOn_comp {Q : (PkgI1.Char2 → ℂ) → ℂ} (hQ : Continuous Q) :
    ContinuousOn (fun τ : ℂ => Q (fun m => PkgI1.thetaConst m (PkgI1.Omega τ))) U :=
  hQ.comp_continuousOn thetaVec_continuousOn

theorem psi4_contOn : ContinuousOn (fun τ : ℂ => psi4Th (PkgI1.Omega τ)) U := contOn_comp continuous_Q4
theorem psi6_contOn : ContinuousOn (fun τ : ℂ => psi6Th (PkgI1.Omega τ)) U := by
  rw [show (fun τ : ℂ => psi6Th (PkgI1.Omega τ)) = fun τ => Q6 (fun m => PkgI1.thetaConst m (PkgI1.Omega τ)) from
    funext fun τ => psi6Th_eq _]
  exact contOn_comp continuous_Q6
theorem chi10_contOn : ContinuousOn (fun τ : ℂ => chi10Th (PkgI1.Omega τ)) U := contOn_comp continuous_Q10
theorem chi12_contOn : ContinuousOn (fun τ : ℂ => chi12Th (PkgI1.Omega τ)) U := by
  rw [show (fun τ : ℂ => chi12Th (PkgI1.Omega τ)) = fun τ => Q12 (fun m => PkgI1.thetaConst m (PkgI1.Omega τ)) from
    funext fun τ => chi12Th_eq _]
  exact contOn_comp continuous_Q12

instance countable_B : Countable PkgI1.B :=
  (QuaternionAlgebra.equivTuple (2 : ℚ) 0 (-3)).injective.countable

/-- `Γ*` is countable (its elements are `ι(x)`, `x ∈ B`). -/
theorem gammaStar_countable : PkgI1.GammaStar.Countable := by
  have h : PkgI1.GammaStar ⊆
      (fun γ : GL (Fin 2) ℝ => (γ : Matrix (Fin 2) (Fin 2) ℝ)) ⁻¹' Set.range PkgI1.iota := by
    rintro γ ⟨x, -, hx, -⟩
    exact ⟨x, hx.symm⟩
  exact ((Set.countable_range _).preimage (fun a b hab => Units.ext hab)).mono h

/-- If the fibres of `j₆` are `Γ*`-orbits, every fibre is countable. -/
theorem fibre_countable {j6 : UpperHalfPlane → OnePoint ℂ}
    (hfib : ∀ τ τ' : UpperHalfPlane, j6 τ = j6 τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ')
    (w : OnePoint ℂ) : {τ | j6 τ = w}.Countable := by
  rcases Set.eq_empty_or_nonempty {τ | j6 τ = w} with h | ⟨τ₀, hτ₀⟩
  · rw [h]; exact Set.countable_empty
  · refine (gammaStar_countable.image (fun γ => γ • τ₀)).mono ?_
    intro τ hτ
    have e : j6 τ₀ = j6 τ := (show j6 τ₀ = w from hτ₀).trans (show j6 τ = w from hτ).symm
    obtain ⟨γ, hγ, hγτ⟩ := (hfib τ₀ τ).1 e
    exact ⟨γ, hγ, hγτ⟩

/-- Two continuous functions on an open `V ⊆ ℂ` that agree off a countable set agree on `V`. -/
theorem eqOn_of_countable {X : Type*} [TopologicalSpace X] [T2Space X] {V : Set ℂ} (hV : IsOpen V)
    {f g : ℂ → X} {S : Set ℂ} (hS : S.Countable) (hf : ContinuousOn f V) (hg : ContinuousOn g V)
    (h : ∀ z ∈ V, z ∉ S → f z = g z) : Set.EqOn f g V :=
  Set.EqOn.of_subset_closure (s := V ∩ Sᶜ) (fun z hz => h z hz.1 hz.2) hf hg Set.inter_subset_left
    ((hS.dense_compl ℂ).open_subset_closure_inter hV)

/-! ## 4. `LinYangThetaCurve` from the printed leaves (eliminating `j₆`) -/

/-- **`LinYangThetaCurve` from Igusa's theta expressions and Lin–Yang's Example 29 (proved).** Where `j₆ = z` is
finite, `s₅ = s₂s₃` and `s₆ = (z+1)s₂³ = s₂³ + s₃²`; the points where `j₆ = ∞` form one `Γ*`-orbit, which is countable,
and both sides are continuous on `ℍ`. -/
theorem linYangThetaCurve_of_printed (hI : IgusaThetaExpressions) (hL : LinYangEx29) :
    LinYangThetaCurve := by
  obtain ⟨j6, -, hfib, -, -, -, -, hrel⟩ := hL
  set S : Set ℂ := (fun τ : UpperHalfPlane => (τ : ℂ)) '' {τ | j6 τ = OnePoint.infty} with hSdef
  have hS : S.Countable := (fibre_countable hfib _).image _
  have hoff : ∀ z ∈ U, z ∉ S →
      psi4Th (PkgI1.Omega z) * psi6Th (PkgI1.Omega z) = 2 ^ 12 * 3 ^ 5 * chi10Th (PkgI1.Omega z) ∧
      psi4Th (PkgI1.Omega z) ^ 3 + psi6Th (PkgI1.Omega z) ^ 2 =
        2 ^ 12 * 3 ^ 6 * chi12Th (PkgI1.Omega z) := by
    intro z hz hzS
    let τ : UpperHalfPlane := ⟨z, hz⟩
    have hne : j6 τ ≠ OnePoint.infty := fun h => hzS ⟨τ, h, rfl⟩
    obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hne
    obtain ⟨h1, h2, h3⟩ := hrel τ w hw.symm
    obtain ⟨e4, e6, e10, e12⟩ := hI _ (omegaSiegel_proof z hz)
    have hτz : ((τ : UpperHalfPlane) : ℂ) = z := rfl
    rw [hτz] at h1 h2 h3
    simp only [lyS2, lyS3, lyS5, lyS6] at h1 h2 h3
    rw [e4, e6] at h1
    rw [e4, e6, e10] at h2
    rw [e4, e12] at h3
    exact ⟨by linear_combination (-1 : ℂ) * h2, by linear_combination h1 - h3⟩
  intro z hz
  have hzU : z ∈ U := hz
  refine ⟨?_, ?_⟩
  · exact eqOn_of_countable isOpen_U hS (psi4_contOn.mul psi6_contOn)
      (continuousOn_const.mul chi10_contOn) (fun z hz hzS => (hoff z hz hzS).1) hzU
  · exact eqOn_of_countable isOpen_U hS ((psi4_contOn.pow 3).add (psi6_contOn.pow 2))
      (continuousOn_const.mul chi12_contOn) (fun z hz hzS => (hoff z hz hzS).2) hzU


/-- **LEAF, strict form (Lin–Yang 2020, Example 29: the relations only).** For every Hauptmodul `j₆` of `Γ*\ℍ`
normalized as in Lin–Yang (continuous, fibres exactly the `Γ*`-orbits, surjective, values `0, ∞, −16/27` at the CM
points of discriminants `−4, −3, −24`; the clauses of `LinYangEx29`), wherever `j₆(τ) = z ≠ ∞`:
`s₃² = z·s₂³`, `s₅ = s₂s₃`, `s₆ = (z + 1)·s₂³`. Unlike `LinYangEx29` it asserts no existence of `j₆`, so it is
Lin–Yang's printed relations and nothing else (sources and faithfulness as for `LinYangEx29`). The Hauptmodul is
supplied by `PkgI1.QMHauptmodul`, which the chain already derives (`linYangEx29_of_all`). -/
def LinYangEx29All : Prop :=
  ∀ j6 : UpperHalfPlane → OnePoint ℂ, Continuous j6 →
    (∀ τ τ' : UpperHalfPlane, j6 τ = j6 τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ') →
    Function.Surjective j6 →
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -1 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = ((0 : ℂ) : OnePoint ℂ)) →
    (∀ x : PkgI1.B, PkgI1.InO x → x * x - x + 1 = 0 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = (OnePoint.infty : OnePoint ℂ)) →
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -6 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = ((-16/27 : ℂ) : OnePoint ℂ)) →
    ∀ τ : UpperHalfPlane, ∀ z : ℂ, j6 τ = (z : OnePoint ℂ) →
      lyS3 (PkgI1.Omega τ) ^ 2 = z * lyS2 (PkgI1.Omega τ) ^ 3 ∧
      lyS5 (PkgI1.Omega τ) = lyS2 (PkgI1.Omega τ) * lyS3 (PkgI1.Omega τ) ∧
      lyS6 (PkgI1.Omega τ) = (z + 1) * lyS2 (PkgI1.Omega τ) ^ 3

/-- The strict form with any Hauptmodul with these clauses (e.g. `PkgI1.QMHauptmodul`'s `f`) gives `LinYangEx29`. -/
theorem linYangEx29_of_all (hA : LinYangEx29All) (hH : PkgI1.QMHauptmodul) : LinYangEx29 := by
  obtain ⟨f, hc, -, hfib, hsurj, h4, h3, h24⟩ := hH
  exact ⟨f, hc, hfib, hsurj, h4, h3, h24, hA f hc hfib hsurj h4 h3 h24⟩

/-- **`LinYangThetaCurve` from Igusa's theta expressions, the strict Lin–Yang leaf and `QMHauptmodul` (proved).** -/
theorem linYangThetaCurve_of_printedAll (hI : IgusaThetaExpressions) (hA : LinYangEx29All)
    (hH : PkgI1.QMHauptmodul) : LinYangThetaCurve :=
  linYangThetaCurve_of_printed hI (linYangEx29_of_all hA hH)

end HDec.HSyn.G0Split.ThetaPt.LinYangPrinted

/-! ## Route 1 from the two printed leaves (linyang-printed §10, theta-fold) -/

namespace HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal

open ThetaGlue ThetaSplit

/-- **The use form of `thetaRatiosAlgebraic` from Igusa's theta expressions and Lin–Yang's Example 29 (proved).** -/
theorem thetaRatiosAtQM_of_printed (hI : LinYangPrinted.IgusaThetaExpressions) (hL : LinYangPrinted.LinYangEx29) :
    ThetaRatiosAtQM :=
  thetaRatiosAtQM_of_linYang (LinYangPrinted.linYangThetaCurve_of_printed hI hL)

/-- **The use form from the strict printed leaves and `QMHauptmodul` (proved; theta-fold).** This is the hypothesis
`hθ` that `HDec.HSyn.gluePieces_of_open4` takes (as a function of `QMHauptmodul`), supplied at the top of the chain
(`sixContactMin_of_open29`) from the added-leaf fields `igusaThetaExpressions` and `linYangEx29All`. -/
theorem thetaRatiosAtQM_of_printedAll (hI : LinYangPrinted.IgusaThetaExpressions)
    (hA : LinYangPrinted.LinYangEx29All) (hH : PkgI1.QMHauptmodul) : ThetaRatiosAtQM :=
  thetaRatiosAtQM_of_printed hI (LinYangPrinted.linYangEx29_of_all hA hH)

/-- **`ThetaPointOfFibre` from `FibreQMPeriod` and the two printed leaves (proved).** Drop-in replacement for
`ThetaPt.thetaPointOfFibre_of_qm_ratios hQM hAlg`. -/
theorem thetaPointOfFibre_of_printed (hQM : FibreQMPeriod) (hI : LinYangPrinted.IgusaThetaExpressions)
    (hL : LinYangPrinted.LinYangEx29) : ThetaPointOfFibre :=
  thetaPointOfFibre_of_linYang hQM (LinYangPrinted.linYangThetaCurve_of_printed hI hL)

/-- **`ThetaPointOfFibre` from `FibreQMPeriod`, `QMHauptmodul` and the strict printed leaves (proved).** -/
theorem thetaPointOfFibre_of_printedAll (hQM : FibreQMPeriod) (hH : PkgI1.QMHauptmodul)
    (hI : LinYangPrinted.IgusaThetaExpressions) (hA : LinYangPrinted.LinYangEx29All) : ThetaPointOfFibre :=
  thetaPointOfFibre_of_linYang hQM (LinYangPrinted.linYangThetaCurve_of_printedAll hI hA hH)

end HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal
