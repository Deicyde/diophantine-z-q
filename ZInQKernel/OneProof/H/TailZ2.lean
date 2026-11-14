import ZInQKernel.OneProof.H.TailO

/-! # OneProof H, leaf-fold8 part 3: qm-split's `Haupt.lean` section (rows H-87, H-88)

`scratch/qm-glue/HauptGlue.lean` (task qm-glue) lines 2198-3687, verbatim: qm-split's section of `Haupt.lean`
(`QMHauptmodulBase3` from the valence formula, the elliptic-order divisibility, Shimizu's covolume). Lines 1-2197 of
`HauptGlue.lean` are leafq-check's `Fold.lean` (lines 1-934, 1326-2563), which is already in `TailO` (leaf-fold6
part f10; checked line by line by `verbatim_check8.py`), so this module imports `TailO` in their place. Generated
by `scratch/leaf-fold8/mk_modules.py`; `#print` lines dropped. -/

set_option linter.all false


/-! ════════════════════════════════════════════════════════════════════════════════════════════
# qm-split: `QMHauptmodulBase3` from the valence formula (published) and three small glue Props

For `c ∈ ℂ` put `H_c = 3779136·G20² − c·G8⁵` (weight 40 for `Γ*`; `jNum∘Ω − c·jDen∘Ω` divided by `dF²⁰`).
The valence formula gives `Σ_{Γ*\ℍ} ord/e = 40·(π/6)/(4π) = 5/3` for `H_c` and `1/3` for `G8`, `5/6` for
`G20`. At `i√3`: `ord G8 ≥ 2` (period-map) and the bound for `G8` force `e = 6`, `ord G8 = 2` and that `G8`
has no other zeros; `ord G20 = a ≤ 4`; so `ord H_c = 2a` there, contributing `a/3`. At every other zero `Q`
of `H_c`, `H_c/G8⁵ = j_θ − c` is `Γ*`-invariant and holomorphic, so `e_Q ∣ ord_Q` (glue
`EllipticOrderDvd`): those contributions are integers. `a/3 + n = 5/3` forces `a = 2`, `n = 1`: the fibre of
`j_θ` over `c` is exactly one orbit. The value `−16/27` is the glue `ThetaQuotientValue24`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

namespace HDec.LeafQCheck.HM.QMSplit

open PkgI1
open HSyn.G0Split.FibreQM.PeriodMap (G8 U tau3 tau4 thetaOmegaAnalytic_proof s8OrderCM3_of
  isOpen_U isPreconnected_U gammaStar_inv)
open UpperHalfPlane (denom denom_ne_zero)
open scoped ENNReal
open Filter Topology

noncomputable section

/-- `G20 = ∏θ²∘Ω/dF¹⁰`. -/
abbrev G20 : ℂ → ℂ := HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20

/-! ## Genuine definitions (as in `Valence.lean`) -/

/-- `e_P` for a general `Γ`: the number of distinct Möbius maps of elements of `Γ` fixing `P`. -/
noncomputable def ellOrderOf (Γ : Set (GL (Fin 2) ℝ)) (P : UpperHalfPlane) : ℕ :=
  Nat.card {f : UpperHalfPlane → UpperHalfPlane // ∃ γ ∈ Γ, γ • P = P ∧ f = fun z => γ • z}

/-- `Γ` acts on `ℍ` as a cocompact Fuchsian group (see `Valence.lean`). -/
structure IsCocompactFuchsian (Γ : Set (GL (Fin 2) ℝ)) : Prop where
  one_mem : 1 ∈ Γ
  mul_mem : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ
  inv_mem : ∀ a ∈ Γ, a⁻¹ ∈ Γ
  det_pos : ∀ a ∈ Γ, 0 < (a : Matrix (Fin 2) (Fin 2) ℝ).det
  properlyDiscontinuous : ∀ K : Set UpperHalfPlane, IsCompact K →
    {f : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ, f = (fun z => γ • z) ∧ (f '' K ∩ K).Nonempty}.Finite
  cocompact : ∃ C : Set UpperHalfPlane, IsCompact C ∧ ∀ z, ∃ γ ∈ Γ, γ • z ∈ C

/-- A fundamental domain of `Γ` on `ℍ` (see `Valence.lean`). -/
def IsFundDomain (Γ : Set (GL (Fin 2) ℝ)) (s : Set UpperHalfPlane) : Prop :=
  MeasurableSet s ∧ (∀ z, ∃ γ ∈ Γ, γ • z ∈ s) ∧
    ∀ γ ∈ Γ, (fun z : UpperHalfPlane => γ • z) ≠ id →
      MeasureTheory.volume (s ∩ (fun z : UpperHalfPlane => γ • z) ⁻¹' s) = 0

/-- Every zero of `F` in `ℍ` is `Γ`-equivalent to a point of `T`. -/
def Covers (Γ : Set (GL (Fin 2) ℝ)) (T : Finset UpperHalfPlane) (F : ℂ → ℂ) : Prop :=
  ∀ z : UpperHalfPlane, F (z : ℂ) = 0 → ∃ t ∈ T, ∃ γ ∈ Γ, γ • t = z

/-- **LEAF (the valence formula for a cocompact Fuchsian group, equality form).** For `Γ` a cocompact
Fuchsian group with fundamental domain `s` and `F` a nonzero holomorphic automorphic form of weight
`k = 2m` (unitary multiplier): the zeros of `F` lie in finitely many `Γ`-orbits, and for a set `T` of
representatives (pairwise inequivalent, covering the zeros) `Σ_{P ∈ T} ord_P(F)/e_P = k·vol(s)/(4π)`; the
same sum over any finite set of pairwise inequivalent points is `≤ k·vol(s)/(4π)`.

Published form: Shimura, *Introduction to the arithmetic theory of automorphic functions*, 1971, Prop. 2.16
and Thm. 2.20 (`Σ_{P ∈ Γ\ℍ} ν_P(F)/e_P = k·vol(Γ\ℍ)/(4π)` for `Γ` of the first kind without cusps; the zeros
are finitely many orbits since `Γ\ℍ` is compact); Rankin, *Modular forms and functions*, 1977, Thm. 4.1.4
(unitary multipliers); numbers UNVERIFIED. The third clause drops nonnegative terms. -/
def ValenceFormulaCocompactEq : Prop :=
  ∀ (Γ : Set (GL (Fin 2) ℝ)), IsCocompactFuchsian Γ → ∀ s, IsFundDomain Γ s →
  ∀ (m : ℕ) (F : ℂ → ℂ), AnalyticOnNhd ℂ F U → (∃ z ∈ U, F z ≠ 0) →
    (∀ γ ∈ Γ, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) →
    (∃ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w) ∧
        Covers Γ T F) ∧
    (∀ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w) →
      Covers Γ T F →
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrderOf Γ z : ℝ≥0∞) =
        (2 * m : ℝ≥0∞) * MeasureTheory.volume s / ENNReal.ofReal (4 * Real.pi)) ∧
    (∀ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w) →
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrderOf Γ z : ℝ≥0∞) ≤
        (2 * m : ℝ≥0∞) * MeasureTheory.volume s / ENNReal.ofReal (4 * Real.pi))

/-- **GLUE (`Γ*` is a cocompact Fuchsian group with covolume `π/6`)**, as in `Valence.lean` (row H-87). -/
def GammaStarCocompactArea : Prop :=
  IsCocompactFuchsian PkgI1.GammaStar ∧
    ∃ s, IsFundDomain PkgI1.GammaStar s ∧ MeasureTheory.volume s = ENNReal.ofReal (Real.pi / 6)

/-- **GLUE (textbook: orders at elliptic points).** If `F₁, F₂` are holomorphic automorphic forms of the same
weight `2m` for `Γ*` (exact automorphy) and `F₂(P) ≠ 0`, then `e_P` divides `ord_P F₁`: `F₁/F₂` is
`Γ*`-invariant and holomorphic at `P`, the stabilizer of `P` acts on a local coordinate `w = (z − P)/(z − P̄)`
by the rotations `w ↦ ζw`, `ζ^{e_P} = 1` (`ζ` primitive), so only powers `w^n` with `e_P ∣ n` occur.
(Shimura 1971, §2.4, the local expansion at elliptic points; Miyake, *Modular forms*, §2.3; UNVERIFIED.) -/
def EllipticOrderDvd : Prop :=
  ∀ (m : ℕ) (F₁ F₂ : ℂ → ℂ), AnalyticOnNhd ℂ F₁ U → AnalyticOnNhd ℂ F₂ U →
    (∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      F₁ ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ m =
        denom γ z ^ (2 * m) * F₁ (z : ℂ)) →
    (∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      F₂ ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ m =
        denom γ z ^ (2 * m) * F₂ (z : ℂ)) →
    ∀ P : UpperHalfPlane, F₂ (P : ℂ) ≠ 0 → analyticOrderAt F₁ (P : ℂ) ≠ ⊤ →
      HDec.LeafQCheck.VB.ellOrder P ∣ (analyticOrderAt F₁ (P : ℂ)).toNat

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


/-! ## Proof -/

abbrev Γs : Set (GL (Fin 2) ℝ) := PkgI1.GammaStar

theorem ellOrderOf_eq : ellOrderOf Γs = HDec.LeafQCheck.VB.ellOrder := rfl

/-- Exact automorphy of weight `2m` for `Γ*`. -/
def Auto (m : ℕ) (F : ℂ → ℂ) : Prop :=
  ∀ γ ∈ Γs, ∀ z : UpperHalfPlane,
    F ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ m =
      denom γ z ^ (2 * m) * F (z : ℂ)

theorem det_ne {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) :
    (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ≠ 0 := by
  obtain ⟨_, _, _, hd⟩ := hγ; exact_mod_cast hd.ne'

theorem zero_iff {m : ℕ} {F : ℂ → ℂ} (hF : Auto m F) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs)
    (z : UpperHalfPlane) : F ((γ • z : UpperHalfPlane) : ℂ) = 0 ↔ F (z : ℂ) = 0 := by
  have e := hF γ hγ z
  constructor
  · intro h
    rw [h, zero_mul] at e
    exact (mul_eq_zero.1 e.symm).resolve_left (pow_ne_zero _ (denom_ne_zero γ z))
  · intro h
    rw [h, mul_zero] at e
    exact (mul_eq_zero.1 e).resolve_right (pow_ne_zero _ (det_ne hγ))

theorem abs_auto {m : ℕ} {F : ℂ → ℂ} (hF : Auto m F) :
    ∀ γ ∈ Γs, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖ := by
  intro γ hγ z
  have ⟨_, _, _, hdet⟩ := hγ
  have e := congrArg norm (hF γ hγ z)
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hdet.le] at e
  simpa using e

theorem auto8 (hT : PkgI1.ThetaModularity) : Auto 4 G8 :=
  HSyn.G0Split.FibreQM.PeriodGlue.s8WeightExact_of hT HDec.LeafQCheck.gammaStarGen_proof

theorem auto20 (hT : PkgI1.ThetaModularity) : Auto 10 G20 :=
  HSyn.G0Split.FibreQM.PeriodGlue.LQ20.s20WeightExact_of hT HDec.LeafQCheck.gammaStarGen_proof

/-- `H_c = 3779136·G20² − c·G8⁵`. -/
def Hc (c : ℂ) (z : ℂ) : ℂ := 3779136 * G20 z ^ 2 - c * G8 z ^ 5

/-- `G8⁵`. -/
def G85 (z : ℂ) : ℂ := G8 z ^ 5

theorem autoHc (hT : PkgI1.ThetaModularity) (c : ℂ) : Auto 20 (Hc c) := by
  intro γ hγ z
  have e1 := auto20 hT γ hγ z
  have e2 := auto8 hT γ hγ z
  simp only [Hc]
  set X := G20 ((γ • z : UpperHalfPlane) : ℂ)
  set Y := G8 ((γ • z : UpperHalfPlane) : ℂ)
  set d := (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ)
  set j := denom γ z
  linear_combination 3779136 * (X * d ^ 10 + j ^ 20 * G20 (z : ℂ)) * e1 -
    c * ((Y * d ^ 4) ^ 4 + (Y * d ^ 4) ^ 3 * (j ^ 8 * G8 (z : ℂ)) +
      (Y * d ^ 4) ^ 2 * (j ^ 8 * G8 (z : ℂ)) ^ 2 + (Y * d ^ 4) * (j ^ 8 * G8 (z : ℂ)) ^ 3 +
      (j ^ 8 * G8 (z : ℂ)) ^ 4) * e2

theorem autoG85 (hT : PkgI1.ThetaModularity) : Auto 20 G85 := by
  intro γ hγ z
  have e2 := auto8 hT γ hγ z
  simp only [G85]
  set Y := G8 ((γ • z : UpperHalfPlane) : ℂ)
  set d := (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ)
  set j := denom γ z
  linear_combination ((Y * d ^ 4) ^ 4 + (Y * d ^ 4) ^ 3 * (j ^ 8 * G8 (z : ℂ)) +
      (Y * d ^ 4) ^ 2 * (j ^ 8 * G8 (z : ℂ)) ^ 2 + (Y * d ^ 4) * (j ^ 8 * G8 (z : ℂ)) ^ 3 +
      (j ^ 8 * G8 (z : ℂ)) ^ 4) * e2

theorem Hc_analytic (c : ℂ) : AnalyticOnNhd ℂ (Hc c) U := fun z hz => by
  unfold Hc
  exact (analyticAt_const.mul ((G20_analytic hz).pow 2)).sub (analyticAt_const.mul ((G8_analytic hz).pow 5))

theorem G85_analytic : AnalyticOnNhd ℂ G85 U := fun z hz => by
  unfold G85; exact (G8_analytic hz).pow 5

/-! ### The equivalence relation of `Γ*` on `ℍ` -/

theorem eqv_symm {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) {z w : UpperHalfPlane} (h : γ • z = w) :
    γ⁻¹ • w = z := by rw [← h, inv_smul_smul]

theorem eqv_trans {γ γ' : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) (hγ' : γ' ∈ Γs) {z w v : UpperHalfPlane}
    (h : γ • z = w) (h' : γ' • w = v) : ∃ δ ∈ Γs, δ • z = v :=
  ⟨γ' * γ, HDec.LeafQCheck.VB.gammaStar_mul hγ' hγ, by rw [mul_smul, h, h']⟩

/-! ### Arithmetic -/

theorem arith (m : ℕ) :
    (2 * m : ℝ≥0∞) * ENNReal.ofReal (Real.pi / 6) / ENNReal.ofReal (4 * Real.pi) = (m : ℝ≥0∞) / 12 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have e1 : (2 * m : ℝ≥0∞) = ENNReal.ofReal (2 * m) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  rw [e1, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
  have e2 : (2 * (m : ℝ) * (Real.pi / 6)) / (4 * Real.pi) = (m : ℝ) / 12 := by
    field_simp; ring
  rw [e2, ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

theorem enn_div (x y : ℕ) (hy : 0 < y) : (x : ℝ≥0∞) / y = ENNReal.ofReal ((x : ℝ) / y) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hy)]; simp

/-! ### The valence formula for `Γ*` -/

section Val

variable (hV : ValenceFormulaCocompactEq) (hA : GammaStarCocompactArea)
include hV hA

theorem val_le (m : ℕ) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F U) (hne : ∃ z ∈ U, F z ≠ 0)
    (hau : Auto m F) (T : Finset UpperHalfPlane)
    (hT : (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w)) :
    ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (HDec.LeafQCheck.VB.ellOrder z : ℝ≥0∞) ≤
      (m : ℝ≥0∞) / 12 := by
  obtain ⟨hFuchs, s, hs, hvol⟩ := hA
  have := (hV Γs hFuchs s hs m F hF hne (abs_auto hau)).2.2 T hT
  rwa [hvol, arith] at this

theorem val_eq (m : ℕ) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F U) (hne : ∃ z ∈ U, F z ≠ 0)
    (hau : Auto m F) (T : Finset UpperHalfPlane)
    (hT : (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w)) (hc : Covers Γs T F) :
    ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (HDec.LeafQCheck.VB.ellOrder z : ℝ≥0∞) =
      (m : ℝ≥0∞) / 12 := by
  obtain ⟨hFuchs, s, hs, hvol⟩ := hA
  have := (hV Γs hFuchs s hs m F hF hne (abs_auto hau)).2.1 T hT hc
  rwa [hvol, arith] at this

theorem val_ex (m : ℕ) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F U) (hne : ∃ z ∈ U, F z ≠ 0)
    (hau : Auto m F) :
    ∃ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w) ∧
      Covers Γs T F := by
  obtain ⟨hFuchs, s, hs, hvol⟩ := hA
  exact (hV Γs hFuchs s hs m F hF hne (abs_auto hau)).1

end Val

/-! ### Facts at `i√3`, `√2 + i`, `τ₂₄` -/

open scoped Classical

theorem pair_ineq {x y : UpperHalfPlane} (h : ∀ γ ∈ Γs, γ • x ≠ y) :
    ((({x, y} : Finset UpperHalfPlane)) : Set UpperHalfPlane).Pairwise
      (fun z w => ∀ γ ∈ Γs, γ • z ≠ w) := by
  intro z hz w hw hzw γ hγ h'
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hz hw
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
  · exact hzw rfl
  · exact h γ hγ h'
  · exact h γ⁻¹ (gammaStar_inv hγ) (eqv_symm hγ h')
  · exact hzw rfl

theorem G8_tau4_ne : G8 (tau4 : ℂ) ≠ 0 := by
  rw [G8_eq]; exact div_ne_zero Sf_tau4 (pow_ne_zero _ (Zf_ne tau4.im_pos))

theorem G8_ne : ∃ z ∈ U, G8 z ≠ 0 := ⟨tau4, tau4.im_pos, G8_tau4_ne⟩

theorem ord_ne_top_of {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) {w : ℂ} (hw : w ∈ U) (hFw : F w ≠ 0)
    (z : UpperHalfPlane) : analyticOrderAt F (z : ℂ) ≠ ⊤ :=
  hF.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_U hw z.im_pos
    (by rw [analyticOrderAt_eq_zero.2 (Or.inr hFw)]; simp)

theorem enn_coe_toNat {o : ℕ∞} (h : o ≠ ⊤) : ((o : ℕ∞) : ℝ≥0∞) = ((o.toNat : ℕ) : ℝ≥0∞) := by
  conv_lhs => rw [← ENat.coe_toNat h]
  simp

variable (hT : PkgI1.ThetaModularity) (hV : ValenceFormulaCocompactEq) (hA : GammaStarCocompactArea)

include hT in
theorem G8_tau3_ge : 2 ≤ analyticOrderAt G8 (tau3 : ℂ) :=
  s8OrderCM3_of thetaOmegaAnalytic_proof (auto8 hT)

include hT hV hA in
/-- `e_{i√3} = 6` and `ord_{i√3} G8 = 2`. -/
theorem tau3_facts : HDec.LeafQCheck.VB.ellOrder tau3 = 6 ∧ analyticOrderAt G8 (tau3 : ℂ) = 2 := by
  have hb2 := G8_tau3_ge hT
  have hbt := ord_ne_top_of (fun z hz => G8_analytic hz) tau4.im_pos G8_tau4_ne tau3
  obtain ⟨he0, he6⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof tau3
  have hle := val_le hV hA 4 G8 (fun z hz => G8_analytic hz) G8_ne (auto8 hT) {tau3}
    (by simp)
  rw [Finset.sum_singleton, enn_coe_toNat hbt, enn_div _ _ he0,
    show ((4 : ℕ) : ℝ≥0∞) / 12 = ((4 : ℕ) : ℝ≥0∞) / ((12 : ℕ) : ℝ≥0∞) by norm_num,
    enn_div 4 12 (by norm_num), ENNReal.ofReal_le_ofReal_iff (by positivity),
    div_le_div_iff₀ (by exact_mod_cast he0) (by norm_num)] at hle
  have hle' : (analyticOrderAt G8 (tau3 : ℂ)).toNat * 12 ≤ 4 * HDec.LeafQCheck.VB.ellOrder tau3 := by
    exact_mod_cast hle
  have hb2' : 2 ≤ (analyticOrderAt G8 (tau3 : ℂ)).toNat := by
    have := ENat.coe_toNat hbt
    rw [← this] at hb2; exact_mod_cast hb2
  refine ⟨by omega, ?_⟩
  rw [← ENat.coe_toNat hbt]
  have : (analyticOrderAt G8 (tau3 : ℂ)).toNat = 2 := by omega
  rw [this]; rfl

include hT in
theorem G8_tau3_zero : G8 (tau3 : ℂ) = 0 := by
  apply apply_eq_zero_of_analyticOrderAt_ne_zero
  intro h0; have := G8_tau3_ge hT; rw [h0] at this; norm_num at this

include hT hV hA in
/-- **`G8` vanishes only on the orbit of `i√3`.** -/
theorem G8_zero_orbit (z : UpperHalfPlane) (hz : G8 (z : ℂ) = 0) : ∃ γ ∈ Γs, γ • tau3 = z := by
  by_contra hno
  push Not at hno
  have hne : tau3 ≠ z := fun h => hno 1 HDec.LeafQCheck.VB.one_mem_gammaStar' (by rw [one_smul, h])
  have hle := val_le hV hA 4 G8 (fun w hw => G8_analytic hw) G8_ne (auto8 hT) {tau3, z}
    (pair_ineq hno)
  rw [Finset.sum_pair hne] at hle
  obtain ⟨he3, hb⟩ := tau3_facts hT hV hA
  have hzt := ord_ne_top_of (fun w hw => G8_analytic hw) tau4.im_pos G8_tau4_ne z
  obtain ⟨hez0, -⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof z
  have ho1 : 1 ≤ (analyticOrderAt G8 (z : ℂ)).toNat := by
    have h1 : analyticOrderAt G8 (z : ℂ) ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]; push Not; exact ⟨G8_analytic z.im_pos, hz⟩
    have h2 : (analyticOrderAt G8 (z : ℂ)).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]; push Not; exact ⟨h1, hzt⟩
    omega
  rw [hb, he3, enn_coe_toNat hzt, enn_div _ _ hez0,
    show ((2 : ℕ∞) : ℝ≥0∞) / ((6 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℕ) / (6 : ℕ)) by
      rw [← enn_div 2 6 (by norm_num)]; simp,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    show ((4 : ℕ) : ℝ≥0∞) / 12 = ((4 : ℕ) : ℝ≥0∞) / ((12 : ℕ) : ℝ≥0∞) by norm_num,
    enn_div 4 12 (by norm_num), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hpos : (0 : ℝ) < ((analyticOrderAt G8 (z : ℂ)).toNat : ℝ) / (HDec.LeafQCheck.VB.ellOrder z : ℝ) := by
    apply div_pos <;> exact_mod_cast (by omega)
  push_cast at hle
  linarith

/-! ### The CM point of discriminant `−24` -/

theorem s9 : (0 : ℝ) < 9 + 6 * √2 := by positivity

/-- `τ₂₄ = i√(9 + 6√2)`. -/
def tau24 : UpperHalfPlane := ⟨(√(9 + 6 * √2) : ℂ) * Complex.I, by simp; positivity⟩

theorem nrd_mu : HDec.LeafQCheck.HM.nrd mu ≠ 0 := by simp [HDec.LeafQCheck.HM.nrd, mu]; norm_num

/-- `ι(μ)` as an element of `GL₂(ℝ)`. -/
def gam24 : GL (Fin 2) ℝ := HDec.LeafQCheck.HM.glOf mu nrd_mu

theorem gam24_coe : (gam24 : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu := HDec.LeafQCheck.HM.coe_glOf mu nrd_mu

theorem tau24_fixed : gam24 • tau24 = tau24 := by
  have hM : (gam24 : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -6 - 3 * √2; 2 - √2, 0] := by
    rw [gam24_coe, iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [mu] <;> ring
  have s2 : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have h2 : √2 < (2 : ℝ) := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hdet : 0 < gam24.det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hM, Matrix.det_fin_two_of]
    nlinarith
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet, div_eq_iff (UpperHalfPlane.denom_ne_zero _ _)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hM, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons]
  have e9 : ((√(9 + 6 * √2) : ℝ) : ℂ) * ((√(9 + 6 * √2) : ℝ) : ℂ) = 9 + 6 * (√2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt s9.le]; push_cast; ring
  have s2c : (√2 : ℂ) * √2 = 2 := by rw [← Complex.ofReal_mul, s2]; norm_num
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  change _ = ((√(9 + 6 * √2) : ℝ) : ℂ) * Complex.I *
    (((2 - √2 : ℝ) : ℂ) * (((√(9 + 6 * √2) : ℝ) : ℂ) * Complex.I) + ((0 : ℝ) : ℂ))
  push_cast
  linear_combination (-(2 - (√2 : ℂ)) * Complex.I * Complex.I) * e9 +
    (-(2 - (√2 : ℂ)) * (9 + 6 * √2)) * hI + (-6) * s2c

variable (hC : ThetaQuotientValue24)

include hC in
theorem G20_tau24_ne : G20 (tau24 : ℂ) ≠ 0 := by
  obtain ⟨hD, hv⟩ := hC gam24 gam24_coe tau24 tau24_fixed
  have hN : PkgI1.jNum (PkgI1.Omega tau24) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hv; norm_num at hv
  change HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 _ ≠ 0
  rw [G20_eq]
  refine div_ne_zero ?_ (pow_ne_zero _ (Zf_ne tau24.im_pos))
  intro hP; apply hN; rw [jNumO_eq, hP]; ring

include hT hV hA hC in
/-- `ord_{i√3} G20 ≤ 4`. -/
theorem G20_tau3_le : (analyticOrderAt G20 (tau3 : ℂ)).toNat ≤ 4 ∧ analyticOrderAt G20 (tau3 : ℂ) ≠ ⊤ := by
  have hG20 : AnalyticOnNhd ℂ G20 U := fun z hz => G20_analytic hz
  have htop := ord_ne_top_of hG20 tau24.im_pos (G20_tau24_ne hC) tau3
  have h4top := ord_ne_top_of hG20 tau24.im_pos (G20_tau24_ne hC) tau4
  refine ⟨?_, htop⟩
  have hineq : ∀ γ ∈ Γs, γ • tau3 ≠ tau4 := by
    intro γ hγ h
    have := (zero_iff (auto8 hT) hγ tau3).2 (G8_tau3_zero hT)
    rw [h] at this; exact G8_tau4_ne this
  have hne : tau3 ≠ tau4 := fun h => hineq 1 HDec.LeafQCheck.VB.one_mem_gammaStar' (by rw [one_smul, h])
  have hle := val_le hV hA 10 G20 hG20 ⟨tau24, tau24.im_pos, G20_tau24_ne hC⟩ (auto20 hT) {tau3, tau4}
    (pair_ineq hineq)
  rw [Finset.sum_pair hne] at hle
  obtain ⟨he3, -⟩ := tau3_facts hT hV hA
  obtain ⟨he40, he46⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof tau4
  have ho1 : 1 ≤ (analyticOrderAt G20 (tau4 : ℂ)).toNat := by
    have h1 : analyticOrderAt G20 (tau4 : ℂ) ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]; push Not
      exact ⟨G20_analytic tau4.im_pos, by
        change HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 _ = 0; rw [G20_eq, Pf_tau4, zero_div]⟩
    have h2 : (analyticOrderAt G20 (tau4 : ℂ)).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]; push Not; exact ⟨h1, h4top⟩
    omega
  rw [he3, enn_coe_toNat htop, enn_coe_toNat h4top, enn_div _ 6 (by norm_num), enn_div _ _ he40,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    show ((10 : ℕ) : ℝ≥0∞) / 12 = ((10 : ℕ) : ℝ≥0∞) / ((12 : ℕ) : ℝ≥0∞) by norm_num,
    enn_div 10 12 (by norm_num), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have h16 : (1 : ℝ) / 6 ≤ ((analyticOrderAt G20 (tau4 : ℂ)).toNat : ℝ) / (HDec.LeafQCheck.VB.ellOrder tau4 : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num) (by exact_mod_cast he40)]
    have : (HDec.LeafQCheck.VB.ellOrder tau4 : ℝ) ≤ 6 := by exact_mod_cast he46
    have : (1 : ℝ) ≤ ((analyticOrderAt G20 (tau4 : ℂ)).toNat : ℝ) := by exact_mod_cast ho1
    nlinarith
  have : ((analyticOrderAt G20 (tau3 : ℂ)).toNat : ℝ) ≤ 4 := by
    push_cast at hle h16 ⊢
    linarith
  exact_mod_cast this

/-! ### The fibres over `c ∈ ℂ` -/

theorem Hc_split (c : ℂ) :
    Hc c = (fun z => 3779136 * G20 z ^ 2) + (fun z => -c * G8 z ^ 5) := by
  funext z; simp only [Hc, Pi.add_apply]; ring

include hT hV hA hC in
theorem ord_Hc_tau3 (c : ℂ) :
    analyticOrderAt (Hc c) (tau3 : ℂ) = ((2 * (analyticOrderAt G20 (tau3 : ℂ)).toNat : ℕ) : ℕ∞) := by
  obtain ⟨he3, hb⟩ := tau3_facts hT hV hA
  obtain ⟨ha4, hatop⟩ := G20_tau3_le hT hV hA hC
  have h3U : (tau3 : ℂ) ∈ U := tau3.im_pos
  have hF : analyticOrderAt (fun z => 3779136 * G20 z ^ 2) (tau3 : ℂ) =
      ((2 * (analyticOrderAt G20 (tau3 : ℂ)).toNat : ℕ) : ℕ∞) := by
    have e : (fun z => 3779136 * G20 z ^ 2) = (fun _ => (3779136 : ℂ)) * G20 ^ 2 := by
      funext z; rfl
    rw [e, analyticOrderAt_mul analyticAt_const ((G20_analytic h3U).pow 2),
      analyticOrderAt_eq_zero.2 (Or.inr (by norm_num)), zero_add,
      analyticOrderAt_pow (G20_analytic h3U), nsmul_eq_mul]
    conv_lhs => rw [← ENat.coe_toNat hatop]
    push_cast; ring
  have hG : (10 : ℕ∞) ≤ analyticOrderAt (fun z => -c * G8 z ^ 5) (tau3 : ℂ) := by
    by_cases hc : c = 0
    · have e : (fun z => -c * G8 z ^ 5) = 0 := by funext z; simp [hc]
      have h0 : analyticOrderAt (0 : ℂ → ℂ) (tau3 : ℂ) = ⊤ :=
        analyticOrderAt_eq_top.2 (Filter.Eventually.of_forall fun _ => rfl)
      rw [e, h0]; exact le_top
    · have e : (fun z => -c * G8 z ^ 5) = (fun _ => -c) * G8 ^ 5 := by funext z; rfl
      rw [e, analyticOrderAt_mul analyticAt_const ((G8_analytic h3U).pow 5),
        analyticOrderAt_eq_zero.2 (Or.inr (by simpa using hc)), zero_add,
        analyticOrderAt_pow (G8_analytic h3U), hb]
      norm_num
  rw [Hc_split, analyticOrderAt_add_eq_left_of_lt, hF]
  rw [hF]
  refine lt_of_lt_of_le ?_ hG
  have : 2 * (analyticOrderAt G20 (tau3 : ℂ)).toNat < 10 := by omega
  exact_mod_cast this

variable (hD : EllipticOrderDvd)

include hT hV hA hC hD in
/-- **The fibre of `j_θ` over `c ∈ ℂ` is one `Γ*`-orbit.** -/
theorem fibre_c (c : ℂ) : ∃ t₁ : UpperHalfPlane, ∀ z : UpperHalfPlane,
    (G8 (z : ℂ) ≠ 0 ∧ Hc c (z : ℂ) = 0) ↔ ∃ γ ∈ Γs, γ • t₁ = z := by
  obtain ⟨he3, hb⟩ := tau3_facts hT hV hA
  obtain ⟨ha4, hatop⟩ := G20_tau3_le hT hV hA hC
  set a := (analyticOrderAt G20 (tau3 : ℂ)).toNat with ha
  have hord := ord_Hc_tau3 hT hV hA hC c
  rw [← ha] at hord
  have hHtop3 : analyticOrderAt (Hc c) (tau3 : ℂ) ≠ ⊤ := by rw [hord]; exact ENat.coe_ne_top _
  have hHtop : ∀ z : UpperHalfPlane, analyticOrderAt (Hc c) (z : ℂ) ≠ ⊤ := fun z =>
    (Hc_analytic c).analyticOrderAt_ne_top_of_isPreconnected isPreconnected_U tau3.im_pos z.im_pos hHtop3
  have hHne : ∃ z ∈ U, Hc c z ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hHtop3
    rw [analyticOrderAt_eq_top]
    filter_upwards [isOpen_U.mem_nhds tau3.im_pos] with z hz using hall z hz
  obtain ⟨T₀, hT₀p, hT₀c⟩ := val_ex hV hA 20 (Hc c) (Hc_analytic c) hHne (autoHc hT c)
  set T₁ := T₀.filter (fun t => ¬ ∃ γ ∈ Γs, γ • t = tau3) with hT₁
  set T' := insert tau3 T₁ with hT'
  have hnot : tau3 ∉ T₁ := by
    rw [hT₁, Finset.mem_filter]; push Not
    intro _; exact ⟨1, HDec.LeafQCheck.VB.one_mem_gammaStar', one_smul _ _⟩
  have hT'p : (T' : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w) := by
    rw [hT', Finset.coe_insert]
    refine (hT₀p.mono (by intro x hx; exact (Finset.mem_filter.1 hx).1)).insert ?_
    intro w hw hne
    have hw' := (Finset.mem_filter.1 hw).2
    refine ⟨fun γ hγ h => hw' ⟨γ⁻¹, gammaStar_inv hγ, eqv_symm hγ h⟩, fun γ hγ h => hw' ⟨γ, hγ, h⟩⟩
  have hT'c : Covers Γs T' (Hc c) := by
    intro z hz
    obtain ⟨t, ht, γ, hγ, rfl⟩ := hT₀c z hz
    by_cases hR : ∃ δ ∈ Γs, δ • t = tau3
    · obtain ⟨δ, hδ, hδt⟩ := hR
      obtain ⟨ε, hε, hεz⟩ := eqv_trans (gammaStar_inv hδ) hγ (eqv_symm hδ hδt) rfl
      exact ⟨tau3, Finset.mem_insert_self _ _, ε, hε, hεz⟩
    · exact ⟨t, Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨ht, hR⟩), γ, hγ, rfl⟩
  have hsum := val_eq hV hA 20 (Hc c) (Hc_analytic c) hHne (autoHc hT c) T' hT'p hT'c
  rw [hT', Finset.sum_insert hnot] at hsum
  -- the points of `T₁`: `G8 ≠ 0`, and `e_t ∣ ord_t H_c`
  have hG8t : ∀ t ∈ T₁, G8 (t : ℂ) ≠ 0 := by
    intro t ht h0
    obtain ⟨γ, hγ, hγt⟩ := G8_zero_orbit hT hV hA t h0
    exact (Finset.mem_filter.1 ht).2 ⟨γ⁻¹, gammaStar_inv hγ, eqv_symm hγ hγt⟩
  have hdvd : ∀ t ∈ T₁, HDec.LeafQCheck.VB.ellOrder t ∣ (analyticOrderAt (Hc c) (t : ℂ)).toNat :=
    fun t ht => hD 20 (Hc c) G85 (Hc_analytic c) G85_analytic (autoHc hT c) (autoG85 hT) t
      (pow_ne_zero 5 (hG8t t ht)) (hHtop t)
  set n : UpperHalfPlane → ℕ := fun t =>
    (analyticOrderAt (Hc c) (t : ℂ)).toNat / HDec.LeafQCheck.VB.ellOrder t with hn
  have hterm : ∀ t ∈ T₁, ((analyticOrderAt (Hc c) (t : ℂ) : ℕ∞) : ℝ≥0∞) /
      (HDec.LeafQCheck.VB.ellOrder t : ℝ≥0∞) = (n t : ℝ≥0∞) := by
    intro t ht
    obtain ⟨he0, -⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof t
    rw [enn_coe_toNat (hHtop t), ← Nat.div_mul_cancel (hdvd t ht)]
    push_cast
    rw [ENNReal.mul_div_cancel_right (by exact_mod_cast he0.ne') (by simp)]
  rw [Finset.sum_congr rfl hterm, hord, he3, ← Nat.cast_sum] at hsum
  set N := ∑ t ∈ T₁, n t
  have key : 2 * a + 6 * N = 10 := by
    have h1 : ((((2 * a : ℕ) : ℕ∞)) : ℝ≥0∞) = ((2 * a : ℕ) : ℝ≥0∞) := by simp
    rw [h1, enn_div _ 6 (by norm_num),
      show ((N : ℕ) : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) by simp,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      show ((20 : ℕ) : ℝ≥0∞) / 12 = ((20 : ℕ) : ℝ≥0∞) / ((12 : ℕ) : ℝ≥0∞) by norm_num,
      enn_div 20 12 (by norm_num), ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at hsum
    push_cast at hsum
    have : (2 * (a : ℝ) + 6 * N) = 10 := by linarith
    exact_mod_cast this
  have hN1 : N = 1 := by omega
  -- the unique point `t₁`
  obtain ⟨t₁, ht₁, hn₁⟩ : ∃ t₁ ∈ T₁, n t₁ ≠ 0 := by
    by_contra h; push Not at h
    have : N = 0 := Finset.sum_eq_zero h
    omega
  have hrest : ∀ t ∈ T₁, t ≠ t₁ → n t = 0 := by
    have hs := Finset.add_sum_erase T₁ n ht₁
    rw [show ∑ x ∈ T₁, n x = N from rfl, hN1] at hs
    have h0 : ∑ x ∈ T₁.erase t₁, n x = 0 := by omega
    intro t ht hne
    exact (Finset.sum_eq_zero_iff.1 h0) t (Finset.mem_erase.2 ⟨hne, ht⟩)
  have hpos : ∀ t ∈ T₁, (Hc c (t : ℂ) = 0 ↔ n t ≠ 0) := by
    intro t ht
    obtain ⟨he0, -⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof t
    have hm := Nat.div_mul_cancel (hdvd t ht)
    constructor
    · intro h0 hn0
      have h1 : analyticOrderAt (Hc c) (t : ℂ) ≠ 0 := by
        rw [Ne, analyticOrderAt_eq_zero]; push Not; exact ⟨Hc_analytic c _ t.im_pos, h0⟩
      have h2 : (analyticOrderAt (Hc c) (t : ℂ)).toNat ≠ 0 := by
        rw [Ne, ENat.toNat_eq_zero]; push Not; exact ⟨h1, hHtop t⟩
      apply h2; rw [← hm]; simp only [n] at hn0; rw [hn0, zero_mul]
    · intro hn0
      apply apply_eq_zero_of_analyticOrderAt_ne_zero
      intro h0
      apply hn0
      simp only [n]; rw [h0]; simp
  refine ⟨t₁, fun z => ⟨fun ⟨hz8, hzH⟩ => ?_, fun ⟨γ, hγ, hγz⟩ => ?_⟩⟩
  · obtain ⟨t, ht, δ, hδ, rfl⟩ := hT'c z hzH
    rw [hT', Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · exact absurd ((zero_iff (auto8 hT) hδ tau3).2 (G8_tau3_zero hT)) hz8
    · have hHt : Hc c (t : ℂ) = 0 := (zero_iff (autoHc hT c) hδ t).1 hzH
      by_cases htt : t = t₁
      · exact ⟨δ, hδ, by rw [← htt]⟩
      · exact absurd ((hpos t ht).1 hHt) (by rw [hrest t ht htt]; simp)
  · subst hγz
    exact ⟨fun h => hG8t t₁ ht₁ ((zero_iff (auto8 hT) hγ t₁).1 h),
      (zero_iff (autoHc hT c) hγ t₁).2 ((hpos t₁ ht₁).2 hn₁)⟩

/-! ### `j_θ` as a map `ℍ → P¹(ℂ)` -/

/-- `j_θ = jNum/jDen ∘ Ω`, with value `∞` where `jDen ∘ Ω = 0`. -/
def jth (τ : UpperHalfPlane) : OnePoint ℂ :=
  if PkgI1.jDen (PkgI1.Omega τ) = 0 then OnePoint.infty
  else ((PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) : ℂ) : OnePoint ℂ)

theorem Sf_eq (z : UpperHalfPlane) : Sf (z : ℂ) = G8 (z : ℂ) * Zf (z : ℂ) ^ 4 := by
  rw [G8_eq, div_mul_cancel₀ _ (pow_ne_zero 4 (Zf_ne z.im_pos))]

theorem Pf_eq (z : UpperHalfPlane) : Pf (z : ℂ) = G20 (z : ℂ) * Zf (z : ℂ) ^ 10 := by
  change Pf (z : ℂ) = HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 (z : ℂ) * Zf (z : ℂ) ^ 10
  rw [G20_eq, div_mul_cancel₀ _ (pow_ne_zero 10 (Zf_ne z.im_pos))]

theorem jDen_zero_iff (z : UpperHalfPlane) : PkgI1.jDen (PkgI1.Omega z) = 0 ↔ G8 (z : ℂ) = 0 := by
  rw [jDenO_eq, Sf_eq]
  constructor
  · intro h
    have := pow_eq_zero_iff (n := 5) (by norm_num) |>.1 h
    exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (Zf_ne z.im_pos))
  · intro h; rw [h]; ring

theorem jth_infty_iff (z : UpperHalfPlane) : jth z = OnePoint.infty ↔ G8 (z : ℂ) = 0 := by
  rw [← jDen_zero_iff]
  unfold jth
  split_ifs with h
  · simp [h]
  · simp [h]

theorem jth_coe_iff (z : UpperHalfPlane) (c : ℂ) : jth z = (c : OnePoint ℂ) ↔
    G8 (z : ℂ) ≠ 0 ∧ Hc c (z : ℂ) = 0 := by
  have hiff := jDen_zero_iff z
  unfold jth
  have hZ := pow_ne_zero 20 (Zf_ne z.im_pos)
  split_ifs with h
  · simp [hiff.1 h]
  · have h8 : G8 (z : ℂ) ≠ 0 := fun h' => h (hiff.2 h')
    simp only [OnePoint.coe_eq_coe, ne_eq, h8, not_false_eq_true, true_and]
    rw [div_eq_iff h, jNumO_eq, jDenO_eq, Sf_eq, Pf_eq]
    constructor
    · intro e
      have : Hc c (z : ℂ) * Zf (z : ℂ) ^ 20 = 0 := by simp only [Hc]; linear_combination e
      exact (mul_eq_zero.1 this).resolve_right hZ
    · intro e
      simp only [Hc] at e
      linear_combination Zf (z : ℂ) ^ 20 * e

include hT hV hA hC hD in
/-- **Every fibre of `j_θ` is one `Γ*`-orbit.** -/
theorem jth_fibre (v : OnePoint ℂ) : ∃ b : UpperHalfPlane, ∀ z : UpperHalfPlane,
    jth z = v ↔ ∃ γ ∈ Γs, γ • b = z := by
  induction v using OnePoint.rec with
  | infty =>
    refine ⟨tau3, fun z => ?_⟩
    rw [jth_infty_iff]
    constructor
    · exact G8_zero_orbit hT hV hA z
    · rintro ⟨γ, hγ, rfl⟩
      exact (zero_iff (auto8 hT) hγ tau3).2 (G8_tau3_zero hT)
  | coe c =>
    obtain ⟨t₁, ht₁⟩ := fibre_c hT hV hA hC hD c
    exact ⟨t₁, fun z => by rw [jth_coe_iff]; exact ht₁ z⟩

include hT in
/-- `j_θ` is `Γ*`-invariant on the finite part (as a function to `ℂ`). -/
theorem g_inv {δ : GL (Fin 2) ℝ} (hδ : δ ∈ Γs) (τ : UpperHalfPlane) :
    PkgI1.jNum (PkgI1.Omega ((δ • τ : UpperHalfPlane) : ℂ)) / PkgI1.jDen (PkgI1.Omega ((δ • τ : UpperHalfPlane) : ℂ)) =
      PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) := by
  have key : ∀ w : UpperHalfPlane, PkgI1.jNum (PkgI1.Omega w) / PkgI1.jDen (PkgI1.Omega w) =
      3779136 * G20 (w : ℂ) ^ 2 / G8 (w : ℂ) ^ 5 := by
    intro w
    rw [jNumO_eq, jDenO_eq, Sf_eq, Pf_eq]
    have hZ := Zf_ne w.im_pos
    by_cases h8 : G8 (w : ℂ) = 0
    · simp [h8]
    · field_simp
  rw [key, key]
  have e1 := auto20 hT δ hδ τ
  have e2 := auto8 hT δ hδ τ
  have hd := det_ne hδ
  have hj := denom_ne_zero δ τ
  by_cases h8 : G8 (τ : ℂ) = 0
  · have h8' : G8 ((δ • τ : UpperHalfPlane) : ℂ) = 0 := (zero_iff (auto8 hT) hδ τ).2 h8
    simp [h8, h8']
  · have h8' : G8 ((δ • τ : UpperHalfPlane) : ℂ) ≠ 0 := fun h => h8 ((zero_iff (auto8 hT) hδ τ).1 h)
    rw [div_eq_div_iff (pow_ne_zero _ h8') (pow_ne_zero _ h8)]
    set X := G20 ((δ • τ : UpperHalfPlane) : ℂ)
    set Y := G8 ((δ • τ : UpperHalfPlane) : ℂ)
    set d := (((δ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ)
    set j := denom δ τ
    have hd20 : d ^ 20 ≠ 0 := pow_ne_zero _ hd
    apply mul_right_cancel₀ hd20
    linear_combination 3779136 * (X * d ^ 10 + j ^ 20 * G20 (τ : ℂ)) * G8 (τ : ℂ) ^ 5 * e1 -
      3779136 * G20 (τ : ℂ) ^ 2 * ((Y * d ^ 4) ^ 4 + (Y * d ^ 4) ^ 3 * (j ^ 8 * G8 (τ : ℂ)) +
        (Y * d ^ 4) ^ 2 * (j ^ 8 * G8 (τ : ℂ)) ^ 2 + (Y * d ^ 4) * (j ^ 8 * G8 (τ : ℂ)) ^ 3 +
        (j ^ 8 * G8 (τ : ℂ)) ^ 4) * e2

theorem jNumO_analytic : AnalyticOnNhd ℂ (fun z => PkgI1.jNum (PkgI1.Omega z)) U :=
  fun z hz => analyticAt_const.mul ((Pf_analytic _ hz).pow 2)

include hT hV hA hC in
/-- `jNum/jDen ∘ Ω → ∞` at `i√3`. -/
theorem pole_tau3 : Tendsto (fun z => PkgI1.jNum (PkgI1.Omega z) / PkgI1.jDen (PkgI1.Omega z))
    (𝓝[≠] (tau3 : ℂ)) (Bornology.cobounded ℂ) := by
  obtain ⟨he3, hb⟩ := tau3_facts hT hV hA
  obtain ⟨ha4, hatop⟩ := G20_tau3_le hT hV hA hC
  have h3U : (tau3 : ℂ) ∈ U := tau3.im_pos
  have hNan := jNumO_analytic _ h3U
  have hDan := jDenO_analytic _ h3U
  have hN : analyticOrderAt (fun z => PkgI1.jNum (PkgI1.Omega z)) (tau3 : ℂ) ≤ 8 := by
    have e : (fun z => PkgI1.jNum (PkgI1.Omega z)) = (fun _ => (3779136 : ℂ)) * Pf ^ 2 := by
      funext z; rfl
    rw [e, analyticOrderAt_mul analyticAt_const ((Pf_analytic _ h3U).pow 2),
      analyticOrderAt_eq_zero.2 (Or.inr (by norm_num)), zero_add,
      analyticOrderAt_pow (Pf_analytic _ h3U), ord_Pf_eq h3U, nsmul_eq_mul]
    change 2 * analyticOrderAt G20 (tau3 : ℂ) ≤ 8
    rw [← ENat.coe_toNat hatop]
    have : 2 * (analyticOrderAt G20 (tau3 : ℂ)).toNat ≤ 8 := by omega
    exact_mod_cast this
  have hD : 10 ≤ analyticOrderAt (fun z => PkgI1.jDen (PkgI1.Omega z)) (tau3 : ℂ) := by
    have e : (fun z => PkgI1.jDen (PkgI1.Omega z)) = Sf ^ 5 := by funext z; rfl
    rw [e, analyticOrderAt_pow (Sf_analytic _ h3U), ord_Sf_eq h3U, hb]
    norm_num
  exact tendsto_cobounded_of_meromorphicOrderAt_neg
    (mero_neg_aux hNan hDan hN hD (jDenO_order_ne_top h3U))

include hT hV hA hC in
theorem jth_continuous : Continuous jth := by
  rw [continuous_iff_continuousAt]
  intro τ₀
  set g : ℂ → ℂ := fun z => PkgI1.jNum (PkgI1.Omega z) / PkgI1.jDen (PkgI1.Omega z) with hg
  by_cases hD0 : PkgI1.jDen (PkgI1.Omega τ₀) = 0
  · have hval : jth τ₀ = OnePoint.infty := by simp [jth, hD0]
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hval]
    obtain ⟨γ, hγ, hγτ⟩ := G8_zero_orbit hT hV hA τ₀ ((jDen_zero_iff τ₀).1 hD0)
    have hpoleH : Tendsto (fun τ : UpperHalfPlane => g τ) (𝓝[≠] tau3) (Bornology.cobounded ℂ) :=
      (pole_tau3 hT hV hA hC).comp (le_of_eq (map_coe_punctured tau3))
    have hback : γ⁻¹ • τ₀ = tau3 := eqv_symm hγ hγτ
    have hmap : Tendsto (fun τ : UpperHalfPlane => γ⁻¹ • τ) (𝓝[≠] τ₀) (𝓝[≠] tau3) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (continuous_const_smul γ⁻¹).tendsto τ₀
        rw [hback] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with τ hτ
        intro h
        apply hτ
        simp only [Set.mem_singleton_iff] at h ⊢
        rw [← hγτ, ← h, smul_inv_smul]
    have hG : Tendsto (fun τ : UpperHalfPlane => g τ) (𝓝[≠] τ₀) (Bornology.cobounded ℂ) := by
      refine (hpoleH.comp hmap).congr (fun τ => ?_)
      simp only [Function.comp, hg]
      have := g_inv hT (gammaStar_inv hγ) τ
      exact this
    have hev : ∀ᶠ τ in 𝓝[≠] τ₀, jth τ = ((g τ : ℂ) : OnePoint ℂ) := by
      filter_upwards [eventually_jDen_ne_H τ₀] with τ hτ
      simp [jth, hτ, hg]
    have hcoe : Tendsto (fun z : ℂ => (z : OnePoint ℂ)) (Bornology.cobounded ℂ) (𝓝 OnePoint.infty) := by
      rw [Metric.cobounded_eq_cocompact, ← Filter.coclosedCompact_eq_cocompact]
      exact OnePoint.tendsto_coe_infty
    exact (hcoe.comp hG).congr' (hev.mono fun τ hτ => hτ.symm)
  · have hcont : ContinuousAt (fun τ : UpperHalfPlane => PkgI1.jDen (PkgI1.Omega τ)) τ₀ :=
      (jDenO_analytic _ τ₀.im_pos).continuousAt.comp UpperHalfPlane.continuous_coe.continuousAt
    have hev : jth =ᶠ[𝓝 τ₀] fun τ => ((g τ : ℂ) : OnePoint ℂ) := by
      filter_upwards [hcont.eventually_ne hD0] with τ hτ
      simp [jth, hτ, hg]
    refine ContinuousAt.congr ?_ hev.symm
    refine OnePoint.continuous_coe.continuousAt.comp ?_
    exact ((jNumO_analytic _ τ₀.im_pos).div (jDenO_analytic _ τ₀.im_pos) hD0).continuousAt.comp
      UpperHalfPlane.continuous_coe.continuousAt

include hT hV hA hC hD in
/-- **Row H-88 from the published valence formula and three glue Props.** -/
theorem qmHauptmodulBase3_of : QMHauptmodulBase3 := by
  refine ⟨jth, jth_continuous hT hV hA hC, fun τ hτ => by simp [jth, hτ], fun τ τ' => ?_,
    fun v => ?_, fun γ hγ τ hτ => ?_⟩
  · obtain ⟨b, hb⟩ := jth_fibre hT hV hA hC hD (jth τ)
    obtain ⟨γ₀, hγ₀, hγ₀b⟩ := (hb τ).1 rfl
    constructor
    · intro h
      obtain ⟨γ₁, hγ₁, hγ₁b⟩ := (hb τ').1 h.symm
      exact eqv_trans (gammaStar_inv hγ₀) hγ₁ (eqv_symm hγ₀ hγ₀b) hγ₁b
    · rintro ⟨γ, hγ, rfl⟩
      obtain ⟨δ, hδ, hδb⟩ := eqv_trans hγ₀ hγ hγ₀b rfl
      exact ((hb _).2 ⟨δ, hδ, hδb⟩).symm
  · obtain ⟨b, hb⟩ := jth_fibre hT hV hA hC hD v
    exact ⟨b, (hb b).2 ⟨1, HDec.LeafQCheck.VB.one_mem_gammaStar', one_smul _ _⟩⟩
  · obtain ⟨hD0, hv⟩ := hC γ hγ τ hτ
    simp only [jth, hD0, if_false, hv]

/-! ### `EllipticOrderDvd` proved (local expansion at an elliptic fixed point) -/

section EllDvd

open HDec.LeafQCheck.VB (zeta zeta_mul zeta_inj zeta_normSq gammaStar_mul one_mem_gammaStar')

/-- `cz + d` on `ℂ`. -/
def dC (γ : GL (Fin 2) ℝ) (z : ℂ) : ℂ :=
  ((γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * z + ((γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ)

/-- The Möbius map on `ℂ`. -/
def Mb (γ : GL (Fin 2) ℝ) (z : ℂ) : ℂ :=
  (((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * z + ((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ)) / dC γ z

theorem dC_coe (γ : GL (Fin 2) ℝ) (z : UpperHalfPlane) : dC γ (z : ℂ) = denom γ z := by
  simp [dC, UpperHalfPlane.denom]

theorem Mb_coe {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) (z : UpperHalfPlane) :
    Mb γ (z : ℂ) = ((γ • z : UpperHalfPlane) : ℂ) := by
  have hd' : 0 < γ.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  rw [UpperHalfPlane.coe_smul_of_det_pos hd', Mb, dC_coe]
  simp [UpperHalfPlane.num]

theorem Mb_sub (γ : GL (Fin 2) ℝ) {z w : ℂ} (hz : dC γ z ≠ 0) (hw : dC γ w ≠ 0) :
    Mb γ z - Mb γ w = (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) * (z - w) / (dC γ z * dC γ w) := by
  rw [Mb, Mb, div_sub_div _ _ hz hw, Matrix.det_fin_two]
  congr 1
  simp only [dC]; push_cast; ring

/-- `det/((cz + d)(cP + d))`, the difference quotient of the Möbius map at `P`. -/
def Rq (γ : GL (Fin 2) ℝ) (P : UpperHalfPlane) (z : ℂ) : ℂ :=
  (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) / (dC γ z * denom γ P)

theorem Rq_P (γ : GL (Fin 2) ℝ) (P : UpperHalfPlane) : Rq γ P (P : ℂ) = zeta γ P := by
  rw [Rq, dC_coe, zeta, sq]

theorem dC_cont (γ : GL (Fin 2) ℝ) : Continuous (dC γ) := by unfold dC; fun_prop

theorem Rq_cont (γ : GL (Fin 2) ℝ) (P : UpperHalfPlane) : ContinuousAt (Rq γ P) (P : ℂ) := by
  unfold Rq
  apply ContinuousAt.div continuousAt_const ((dC_cont γ).continuousAt.mul continuousAt_const)
  show dC γ (P : ℂ) * denom γ P ≠ 0
  rw [dC_coe]; exact mul_ne_zero (denom_ne_zero γ P) (denom_ne_zero γ P)

theorem Mb_cont (γ : GL (Fin 2) ℝ) (P : UpperHalfPlane) : ContinuousAt (Mb γ) (P : ℂ) := by
  unfold Mb
  apply ContinuousAt.div (by fun_prop) (dC_cont γ).continuousAt
  rw [dC_coe]; exact denom_ne_zero γ P

/-- `Mb γ z − P = Rq(z)·(z − P)` near `P`, for `γ` fixing `P`. -/
theorem Mb_sub_P {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) {P : UpperHalfPlane}
    (hP : γ • P = P) {z : ℂ} (hz : dC γ z ≠ 0) : Mb γ z - (P : ℂ) = Rq γ P z * (z - P) := by
  have hP' : Mb γ (P : ℂ) = (P : ℂ) := by rw [Mb_coe hd, hP]
  have hdP : dC γ (P : ℂ) ≠ 0 := by rw [dC_coe]; exact denom_ne_zero γ P
  conv_lhs => rw [← hP']
  rw [Mb_sub γ hz hdP, Rq, dC_coe]
  field_simp [denom_ne_zero γ P]

theorem eq_at_of_punctured {f g : ℂ → ℂ} {P : ℂ} (hf : ContinuousAt f P) (hg : ContinuousAt g P)
    (h : f =ᶠ[𝓝[≠] P] g) : f P = g P :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

/-- **The multiplier depends only on the Möbius map.** -/
theorem zeta_congr {γ γ' : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hd' : 0 < (γ' : Matrix (Fin 2) (Fin 2) ℝ).det) {P : UpperHalfPlane} (hP : γ • P = P)
    (hP' : γ' • P = P) (h : ∀ z : UpperHalfPlane, γ • z = γ' • z) : zeta γ P = zeta γ' P := by
  rw [← Rq_P, ← Rq_P]
  apply eq_at_of_punctured (Rq_cont γ P) (Rq_cont γ' P)
  have hU : ∀ᶠ z in 𝓝[≠] (P : ℂ), z ∈ U ∧ z ≠ (P : ℂ) ∧ dC γ z ≠ 0 ∧ dC γ' z ≠ 0 := by
    have h1 : ∀ᶠ z in 𝓝 (P : ℂ), z ∈ U := isOpen_U.mem_nhds P.im_pos
    have h2 : ∀ᶠ z in 𝓝 (P : ℂ), dC γ z ≠ 0 :=
      (dC_cont γ).continuousAt.eventually_ne (by rw [dC_coe]; exact denom_ne_zero γ P)
    have h3 : ∀ᶠ z in 𝓝 (P : ℂ), dC γ' z ≠ 0 :=
      (dC_cont γ').continuousAt.eventually_ne (by rw [dC_coe]; exact denom_ne_zero γ' P)
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, nhdsWithin_le_nhds h3,
      self_mem_nhdsWithin] with z a b c d
    exact ⟨a, d, b, c⟩
  filter_upwards [hU] with z ⟨hzU, hzP, h1, h2⟩
  have e1 := Mb_sub_P hd hP h1
  have e2 := Mb_sub_P hd' hP' h2
  have e3 : Mb γ z = Mb γ' z := by
    have k1 := Mb_coe hd ⟨z, hzU⟩
    have k2 := Mb_coe hd' ⟨z, hzU⟩
    have k3 := congrArg (fun w : UpperHalfPlane => (w : ℂ)) (h ⟨z, hzU⟩)
    exact k1.trans (k3.trans k2.symm)
  rw [e3, e2] at e1
  exact (mul_right_cancel₀ (sub_ne_zero.2 hzP) e1).symm

/-- **The multiplier is an `n`-th root of unity, `n = ord_P F₁`.** -/
theorem zeta_pow_ord {m : ℕ} {F₁ F₂ : ℂ → ℂ} (hF₁ : AnalyticOnNhd ℂ F₁ U) (hF₂ : AnalyticOnNhd ℂ F₂ U)
    (h₁ : Auto m F₁) (h₂ : Auto m F₂) {P : UpperHalfPlane} (hF₂P : F₂ (P : ℂ) ≠ 0) {n : ℕ}
    (hn : analyticOrderAt F₁ (P : ℂ) = n) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) (hP : γ • P = P) :
    zeta γ P ^ n = 1 := by
  have hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det := by obtain ⟨_, _, _, hd⟩ := hγ; exact hd
  obtain ⟨g, hg, hg0, hfact⟩ := ((hF₁ _ P.im_pos).analyticOrderAt_eq_natCast).1 hn
  have hP' : Mb γ (P : ℂ) = (P : ℂ) := by rw [Mb_coe hd, hP]
  have hMt : Tendsto (Mb γ) (𝓝 (P : ℂ)) (𝓝 (P : ℂ)) := by
    have := (Mb_cont γ P).tendsto; rwa [hP'] at this
  -- the cross relation `F₁(γz) F₂(z) = F₁(z) F₂(γz)`
  have hcross : ∀ z : UpperHalfPlane, F₁ (Mb γ z) * F₂ z = F₁ z * F₂ (Mb γ z) := by
    intro z
    have e1 := h₁ γ hγ z
    have e2 := h₂ γ hγ z
    rw [← Mb_coe hd] at e1 e2
    have hdm := pow_ne_zero m (det_ne hγ)
    apply mul_right_cancel₀ hdm
    linear_combination F₂ (z : ℂ) * e1 - F₁ (z : ℂ) * e2
  have hev : ∀ᶠ z in 𝓝[≠] (P : ℂ),
      Rq γ P z ^ n * (g (Mb γ z) * F₂ z) = g z * F₂ (Mb γ z) := by
    have h1 : ∀ᶠ z in 𝓝 (P : ℂ), z ∈ U := isOpen_U.mem_nhds P.im_pos
    have h2 : ∀ᶠ z in 𝓝 (P : ℂ), dC γ z ≠ 0 :=
      (dC_cont γ).continuousAt.eventually_ne (by rw [dC_coe]; exact denom_ne_zero γ P)
    have h3 : ∀ᶠ z in 𝓝 (P : ℂ), F₁ (Mb γ z) = (Mb γ z - P) ^ n • g (Mb γ z) := hMt.eventually hfact
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, nhdsWithin_le_nhds h3,
      nhdsWithin_le_nhds hfact, self_mem_nhdsWithin] with z hzU hdz h3z hfz hzP
    have hc := hcross ⟨z, hzU⟩
    simp only at hc
    rw [h3z, hfz, Mb_sub_P hd hP hdz, smul_eq_mul, smul_eq_mul, mul_pow] at hc
    have hzP' : (z - P) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hzP)
    apply mul_left_cancel₀ hzP'
    linear_combination hc
  have hL : ContinuousAt (fun z => Rq γ P z ^ n * (g (Mb γ z) * F₂ z)) (P : ℂ) := by
    refine ((Rq_cont γ P).pow n).mul (ContinuousAt.mul ?_ (hF₂ _ P.im_pos).continuousAt)
    exact ContinuousAt.comp (by rw [hP']; exact hg.continuousAt) (Mb_cont γ P)
  have hR : ContinuousAt (fun z => g z * F₂ (Mb γ z)) (P : ℂ) := by
    refine hg.continuousAt.mul ?_
    exact ContinuousAt.comp (by rw [hP']; exact (hF₂ _ P.im_pos).continuousAt) (Mb_cont γ P)
  have heq := eq_at_of_punctured hL hR hev
  simp only [hP', Rq_P] at heq
  have hne : g (P : ℂ) * F₂ (P : ℂ) ≠ 0 := mul_ne_zero hg0 hF₂P
  have : (zeta γ P ^ n - 1) * (g (P : ℂ) * F₂ (P : ℂ)) = 0 := by linear_combination heq
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

theorem zeta_one (P : UpperHalfPlane) : zeta 1 P = 1 := by
  simp [zeta, UpperHalfPlane.denom]

theorem zeta_ne_zero {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) : zeta γ P ≠ 0 := by
  intro h; have := zeta_normSq hd hP; rw [h] at this; simp at this

/-- **`EllipticOrderDvd` is a theorem.** -/
theorem ellipticOrderDvd_proof : EllipticOrderDvd := by
  intro m F₁ F₂ hF₁ hF₂ h₁ h₂ P hF₂P htop
  set n := (analyticOrderAt F₁ (P : ℂ)).toNat
  have hn : analyticOrderAt F₁ (P : ℂ) = n := (ENat.coe_toNat htop).symm
  have hdet : ∀ γ ∈ Γs, 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det := fun γ ⟨_, _, _, hd⟩ => hd
  -- the multiplier group
  let H : Subgroup ℂˣ :=
    { carrier := {u | ∃ γ ∈ Γs, γ • P = P ∧ (u : ℂ) = zeta γ P}
      one_mem' := ⟨1, one_mem_gammaStar', one_smul _ _, by simp [zeta_one]⟩
      mul_mem' := by
        rintro u v ⟨γ, hγ, hP, hu⟩ ⟨γ', hγ', hP', hv⟩
        refine ⟨γ * γ', gammaStar_mul hγ hγ', by rw [mul_smul, hP', hP], ?_⟩
        rw [Units.val_mul, hu, hv, zeta_mul (hdet _ hγ) (hdet _ hγ') hP']
      inv_mem' := by
        rintro u ⟨γ, hγ, hP, hu⟩
        refine ⟨γ⁻¹, gammaStar_inv hγ, by rw [inv_smul_eq_iff, hP], ?_⟩
        have hm := zeta_mul (hdet _ (gammaStar_inv hγ)) (hdet _ hγ) hP
        rw [inv_mul_cancel, zeta_one] at hm
        have hz := zeta_ne_zero (hdet _ hγ) hP
        rw [Units.val_inv_eq_inv_val, hu]
        field_simp
        linear_combination hm }
  set S := {f : UpperHalfPlane → UpperHalfPlane //
    ∃ γ ∈ PkgI1.GammaStar, γ • P = P ∧ f = fun z => γ • z}
  -- `S ≃ H`
  let Ψ : S → H := fun f =>
    ⟨Units.mk0 (zeta (Classical.choose f.2) P)
      (zeta_ne_zero (hdet _ (Classical.choose_spec f.2).1) (Classical.choose_spec f.2).2.1),
      ⟨_, (Classical.choose_spec f.2).1, (Classical.choose_spec f.2).2.1, rfl⟩⟩
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro f f' hff
      have h := congrArg (fun u : H => ((u : ℂˣ) : ℂ)) hff
      simp only [Ψ, Units.val_mk0] at h
      obtain ⟨hγ, hP, hf⟩ := Classical.choose_spec f.2
      obtain ⟨hγ', hP', hf'⟩ := Classical.choose_spec f'.2
      apply Subtype.ext
      rw [hf, hf']
      funext z
      exact zeta_inj (hdet _ hγ) (hdet _ hγ') hP hP' h z
    · rintro ⟨u, γ, hγ, hP, hu⟩
      refine ⟨⟨fun z => γ • z, γ, hγ, hP, rfl⟩, ?_⟩
      apply Subtype.ext; apply Units.ext
      simp only [Ψ, Units.val_mk0]
      obtain ⟨hγ', hP', hf'⟩ := Classical.choose_spec
        (⟨fun z => γ • z, γ, hγ, hP, rfl⟩ : S).2
      rw [hu]
      exact zeta_congr (hdet _ hγ') (hdet _ hγ) hP' hP (fun z => (congrFun hf' z).symm)
  have hcard : Nat.card H = HDec.LeafQCheck.VB.ellOrder P :=
    (Nat.card_congr (Equiv.ofBijective Ψ hΨ)).symm
  obtain ⟨he0, -⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof P
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  rw [← hcard, ← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  rintro ⟨u, γ, hγ, hP, hu⟩
  apply Subtype.ext; apply Units.ext
  simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
  rw [hu]
  exact zeta_pow_ord hF₁ hF₂ h₁ h₂ hF₂P hn hγ hP

end EllDvd

include hT hV hA hC in
/-- **Row H-88 with `EllipticOrderDvd` discharged**: from the valence formula (LEAF), the covolume glue and
the CM-value glue (and the bundle leaf `r4`). -/
theorem qmHauptmodulBase3_of' : QMHauptmodulBase3 :=
  qmHauptmodulBase3_of hT hV hA hC ellipticOrderDvd_proof

include hV hA in
/-- **Row H-87 from the same leaf and glue** (the inequality clause of the valence formula; the chain-level
copy `HDec.LeafQCheck.VB.ValenceFormulaGammaStar` of leafq-check's row). -/
theorem valenceFormulaGammaStar_of_eq : HDec.LeafQCheck.VB.ValenceFormulaGammaStar := by
  intro m F hF hne haut T hT
  obtain ⟨hFuchs, s, hs, hvol⟩ := hA
  have := (hV Γs hFuchs s hs m F hF hne haut).2.2 T hT
  rwa [hvol, arith] at this


/-! ### The covolume glue split: Shimizu's formula for `𝒪¹` (LEAF) and the passage to `Γ*` (GLUE) -/

/-- `Γ¹ = ι(𝒪¹)`: the images of the norm-one units of `𝒪` (`det ι(x) = nrd(x)`). -/
def Gamma1 : Set (GL (Fin 2) ℝ) :=
  {γ | ∃ x : PkgI1.B, PkgI1.InO x ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧
    (γ : Matrix (Fin 2) (Fin 2) ℝ).det = 1}

/-- **LEAF (Shimura; Shimizu's volume formula).** `Γ¹ = ι(𝒪¹)`, for the maximal order `𝒪` of the indefinite
division algebra `B` of discriminant `6`, is a cocompact Fuchsian group, with a fundamental domain of
hyperbolic area `(π/3) ∏_{p | 6} (p − 1) = 2π/3`. Shimura, *Introduction to the arithmetic theory of
automorphic functions*, 1971, Prop. 9.2 (cocompactness); H. Shimizu, *On zeta functions of quaternion
algebras*, Ann. of Math. 81 (1965) (volume); Vignéras, *Arithmétique des algèbres de quaternions*, LNM 800,
IV §1; Voight, *Quaternion algebras*, Thm 39.1.13; locators UNVERIFIED. -/
def ShimizuCovolumeO1 : Prop :=
  IsCocompactFuchsian Gamma1 ∧
    ∃ s, IsFundDomain Gamma1 s ∧ MeasureTheory.volume s = ENNReal.ofReal (2 * Real.pi / 3)

/-- **GLUE (from `𝒪¹` to `Γ*`).** Shimizu's statement for `Γ¹` gives `GammaStarCocompactArea`. What it needs:
`Γ¹ ⊆ Γ*`, the index `[Γ* : ℚ^×Γ¹] = 4` of the Möbius groups (`N_B(𝒪)⁺/ℚ^×𝒪^×₊ ≅ W`, representatives
`1, x₄, x₆, x₄x₆` up to `𝒪¹`; `GammaStarGen` and the chain's `tt` representatives), proper discontinuity and
cocompactness of a finite-index supergroup, and the comparison of fundamental domains (area divided by the
index). Project glue (measure theory and an index computation). -/
def GammaStarFromO1 : Prop := ShimizuCovolumeO1 → GammaStarCocompactArea

/-! ### `GammaStarFromO1` bypassed for H-87: the valence formula for `Γ¹` and an index argument

For `z` and the four coset representatives `g_i = ι(1), ι(a4), ι(a6), ι(a4 a6)` of `Γ¹` in `Γ*` (reduced norms
`1, 2, 3, 6`, pairwise in distinct cosets), the points `g_i z` fall into `r_z` classes of `Γ¹`-equivalence with
`4 e¹_z ≤ r_z e*_z`; the valence bound for `Γ¹` (Shimizu: total `m/3`) over these points gives
`4 Σ ord/e* ≤ m/3`. -/

section Index

open HDec.LeafQCheck.VB (gammaStar_mul one_mem_gammaStar')

theorem inO_ofInt (x : PkgI1.B) : PkgI1.InO x ↔ ∃ n : Fin 4 → ℤ, x = LeafQM.ofInt n := by
  rw [inO_iff]
  constructor
  · rintro ⟨n0, n1, n2, n3, rfl⟩
    exact ⟨![n0, n1, n2, n3], by ext <;> simp [LeafQM.ofInt]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n 0, n 1, n 2, n 3, by ext <;> simp [LeafQM.ofInt]⟩

theorem inO_mul {x y : PkgI1.B} (hx : PkgI1.InO x) (hy : PkgI1.InO y) : PkgI1.InO (x * y) := by
  obtain ⟨n, rfl⟩ := (inO_ofInt x).1 hx
  obtain ⟨m, rfl⟩ := (inO_ofInt y).1 hy
  exact (inO_ofInt _).2 ⟨_, LeafQM.ofInt_mul n m⟩

theorem inO_one : PkgI1.InO (1 : PkgI1.B) :=
  (inO_ofInt _).2 ⟨![1, 0, 0, 0], by ext <;> simp [LeafQM.ofInt]⟩

theorem inO_star {x : PkgI1.B} (hx : PkgI1.InO x) : PkgI1.InO (star x) := by
  obtain ⟨n, rfl⟩ := (inO_ofInt x).1 hx
  exact (inO_ofInt _).2 ⟨![n 0 + n 2, -n 1, -n 2, -n 3], by ext <;> simp [LeafQM.ofInt] <;> ring⟩

theorem mul_star_nrd (x : PkgI1.B) : x * star x = ((nrd x : ℚ) : PkgI1.B) := by
  rw [QuaternionAlgebra.mul_star_eq_coe]; congr 1; simp [nrd]; ring

theorem star_mul_nrd (x : PkgI1.B) : star x * x = ((nrd x : ℚ) : PkgI1.B) := by
  rw [QuaternionAlgebra.star_mul_eq_coe]; congr 1; simp [nrd]; ring

/-- `Γ¹` as a subgroup of `GL₂(ℝ)`. -/
def G1 : Subgroup (GL (Fin 2) ℝ) where
  carrier := Gamma1
  one_mem' := ⟨1, inO_one, by rw [iota_one]; rfl, by simp⟩
  mul_mem' := by
    rintro a b ⟨x, hx, hax, hda⟩ ⟨y, hy, hby, hdb⟩
    exact ⟨x * y, inO_mul hx hy, by rw [Units.val_mul, hax, hby, iota_mul],
      by rw [Units.val_mul, Matrix.det_mul, hda, hdb, one_mul]⟩
  inv_mem' := by
    rintro a ⟨x, hx, hax, hda⟩
    have hn : nrd x = 1 := by
      have := hda; rw [hax, det_iota_eq] at this; exact_mod_cast this
    refine ⟨star x, inO_star hx, ?_, ?_⟩
    · have h1 : (a : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota (star x) = 1 := by
        rw [hax, ← iota_mul, mul_star_nrd, hn]; simpa using iota_one
      have := congrArg (fun M => (((a⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) * M) h1
      simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, mul_one] at this
      exact this.symm
    · rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.det_nonsing_inv, hda, Ring.inverse_one]

/-- `Γ*` as a subgroup of `GL₂(ℝ)`. -/
def Gs : Subgroup (GL (Fin 2) ℝ) where
  carrier := Γs
  one_mem' := one_mem_gammaStar'
  mul_mem' := fun ha hb => gammaStar_mul ha hb
  inv_mem' := fun ha => gammaStar_inv ha

theorem G1_le : G1 ≤ Gs := by
  rintro a ⟨x, hx, hax, hda⟩
  have hn : nrd x = 1 := by
    have := hda; rw [hax, det_iota_eq] at this; exact_mod_cast this
  refine ⟨x, ⟨star x, by rw [mul_star_nrd, hn]; simp, by rw [star_mul_nrd, hn]; simp,
    fun z hz => ⟨inO_mul (inO_mul hx hz) (inO_star hx), inO_mul (inO_mul (inO_star hx) hz) hx⟩⟩,
    hax, by rw [hda]; norm_num⟩

theorem G1_normal {γ h : GL (Fin 2) ℝ} (hγ : γ ∈ Gs) (hh : h ∈ G1) : γ * h * γ⁻¹ ∈ G1 := by
  obtain ⟨x, ⟨y, hxy, hyx, hN⟩, hγx, hd⟩ := hγ
  obtain ⟨w, hw, hhw, hdw⟩ := hh
  have hinv : ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota y := by
    have h1 : (γ : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota y = 1 := by
      rw [hγx, ← iota_mul, hxy, iota_one]
    have := congrArg (fun M => (((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) * M) h1
    simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, mul_one] at this
    exact this.symm
  refine ⟨x * w * y, (hN w hw).1, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, hγx, hhw, hinv, iota_mul, iota_mul]
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdw, mul_one, ← Matrix.det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

/-- The Möbius action as permutations. -/
abbrev mob : GL (Fin 2) ℝ →* Equiv.Perm UpperHalfPlane := MulAction.toPermHom _ _

def Mstar : Subgroup (Equiv.Perm UpperHalfPlane) := Gs.map mob
def Mone : Subgroup (Equiv.Perm UpperHalfPlane) := G1.map mob

theorem Mone_normal {σ τ : Equiv.Perm UpperHalfPlane} (hσ : σ ∈ Mstar) (hτ : τ ∈ Mone) :
    σ * τ * σ⁻¹ ∈ Mone := by
  obtain ⟨γ, hγ, rfl⟩ := hσ
  obtain ⟨h, hh, rfl⟩ := hτ
  exact ⟨γ * h * γ⁻¹, G1_normal hγ hh, by simp [map_mul, map_inv]⟩

/-- Stabilizers. -/
def Sstar (z : UpperHalfPlane) : Subgroup (Equiv.Perm UpperHalfPlane) :=
  Mstar ⊓ MulAction.stabilizer (Equiv.Perm UpperHalfPlane) z
def Sone (z : UpperHalfPlane) : Subgroup (Equiv.Perm UpperHalfPlane) :=
  Mone ⊓ MulAction.stabilizer (Equiv.Perm UpperHalfPlane) z

theorem card_Sstar (z : UpperHalfPlane) : Nat.card (Sstar z) = HDec.LeafQCheck.VB.ellOrder z := by
  unfold HDec.LeafQCheck.VB.ellOrder
  refine Nat.card_congr (Equiv.ofBijective (fun σ => ⟨⇑(σ : Equiv.Perm UpperHalfPlane), ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨⟨γ, hγ, hσ⟩, hz⟩ := σ.2
    refine ⟨γ, hγ, ?_, ?_⟩
    · have : (σ : Equiv.Perm UpperHalfPlane) z = z := hz
      rw [← hσ] at this; exact this
    · rw [← hσ]; rfl
  · intro σ τ h
    apply Subtype.ext; apply Equiv.ext; intro w
    exact congrFun (congrArg Subtype.val h) w
  · rintro ⟨f, γ, hγ, hz, rfl⟩
    exact ⟨⟨mob γ, ⟨γ, hγ, rfl⟩, hz⟩, rfl⟩

theorem card_Sone (z : UpperHalfPlane) : Nat.card (Sone z) = ellOrderOf Gamma1 z := by
  unfold ellOrderOf
  refine Nat.card_congr (Equiv.ofBijective (fun σ => ⟨⇑(σ : Equiv.Perm UpperHalfPlane), ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨⟨γ, hγ, hσ⟩, hz⟩ := σ.2
    refine ⟨γ, hγ, ?_, ?_⟩
    · have : (σ : Equiv.Perm UpperHalfPlane) z = z := hz
      rw [← hσ] at this; exact this
    · rw [← hσ]; rfl
  · intro σ τ h
    apply Subtype.ext; apply Equiv.ext; intro w
    exact congrFun (congrArg Subtype.val h) w
  · rintro ⟨f, γ, hγ, hz, rfl⟩
    exact ⟨⟨mob γ, ⟨γ, hγ, rfl⟩, hz⟩, rfl⟩

theorem Sone_le (z : UpperHalfPlane) : Sone z ≤ Sstar z :=
  inf_le_inf_right _ (Subgroup.map_mono G1_le)

/-- `e¹` is constant along `Γ*`-orbits (`Γ¹` is normal in `Γ*`). -/
theorem card_Sone_smul {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Gs) (z : UpperHalfPlane) :
    Nat.card (Sone (γ • z)) = Nat.card (Sone z) := by
  have hσ : mob γ ∈ Mstar := ⟨γ, hγ, rfl⟩
  have hσi : (mob γ)⁻¹ ∈ Mstar := Mstar.inv_mem hσ
  refine Nat.card_congr ⟨fun τ => ⟨(mob γ)⁻¹ * τ * mob γ, ?_, ?_⟩,
    fun τ => ⟨mob γ * τ * (mob γ)⁻¹, ?_, ?_⟩, ?_, ?_⟩
  · have := Mone_normal hσi τ.2.1; rwa [inv_inv] at this
  · change ((mob γ)⁻¹ * τ * mob γ) z = z
    have hτ : (τ : Equiv.Perm UpperHalfPlane) (γ • z) = γ • z := τ.2.2
    simp only [Equiv.Perm.coe_mul, Function.comp]
    change (mob γ)⁻¹ ((τ : Equiv.Perm UpperHalfPlane) (γ • z)) = z
    rw [hτ]; simp
  · exact Mone_normal hσ τ.2.1
  · change (mob γ * τ * (mob γ)⁻¹) (γ • z) = γ • z
    have hτ : (τ : Equiv.Perm UpperHalfPlane) z = z := τ.2.2
    simp only [Equiv.Perm.coe_mul, Function.comp]
    have e : (mob γ)⁻¹ (γ • z) = z := by simp
    rw [e, hτ]; rfl
  · intro τ; apply Subtype.ext; simp [mul_assoc]
  · intro τ; apply Subtype.ext; simp [mul_assoc]

/-- The four coset representatives `1, a4, a6, a4 a6` (reduced norms `1, 2, 3, 6`) and their inverses. -/
def rep4 : Fin 4 → PkgI1.B := ![1, a4, a6, a4 * a6]
def rep4i : Fin 4 → PkgI1.B := ![1, a4i, a6i, a6i * a4i]

theorem nd_rep (i : Fin 4) : NormData (rep4 i) (rep4i i) := by
  fin_cases i
  · exact NormData.one
  · exact nd_a4
  · exact nd_a6
  · exact nd_a4.mul nd_a6

def g4 (i : Fin 4) : GL (Fin 2) ℝ := glOf (rep4 i) (nd_rep i).2.2.2.ne'

theorem g4_mem (i : Fin 4) : g4 i ∈ Gs := glOf_mem (nd_rep i)

theorem nrd_rep (i : Fin 4) : nrd (rep4 i) = ((![1, 2, 3, 6] : Fin 4 → ℤ) i : ℚ) := by
  fin_cases i <;> simp [rep4, nrd_mul, nrd, a4, a6] <;> norm_num

theorem g4_inv_coe (i : Fin 4) :
    (((g4 i)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota (rep4i i) := by
  have h1 : ((g4 i : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota (rep4i i) = 1 := by
    rw [g4, coe_glOf, ← iota_mul, (nd_rep i).1, iota_one]
  have := congrArg (fun M => ((((g4 i)⁻¹ : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) * M) h1
  simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, mul_one] at this
  exact this.symm

/-- A matrix of positive determinant acting trivially on `ℍ` is scalar. -/
theorem scalar_of_trivial {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    (h : ∀ z : UpperHalfPlane, γ • z = z) :
    (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
  have hd' : 0 < γ.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  have key : ∀ z : UpperHalfPlane,
      ((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * z + ((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) =
        (z : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * z + ((γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ)) := by
    intro z
    have e : ((γ • z : UpperHalfPlane) : ℂ) = (z : ℂ) := congrArg (fun w : UpperHalfPlane => (w : ℂ)) (h z)
    rw [UpperHalfPlane.coe_smul_of_det_pos hd', div_eq_iff (denom_ne_zero γ z)] at e
    simpa [UpperHalfPlane.num, UpperHalfPlane.denom, mul_comm] using e
  have k1 := key UpperHalfPlane.I
  have k2 := key ⟨2 * Complex.I, by simp⟩
  simp only [UpperHalfPlane.coe_I] at k1
  simp only [UpperHalfPlane.coe_mk] at k2
  have r1 := congrArg Complex.re k1; have i1 := congrArg Complex.im k1
  have r2 := congrArg Complex.re k2
  simp at r1 i1 r2
  refine ⟨by linarith, by linarith, by linarith⟩

theorem rat_of_scalar {u : PkgI1.B} (h10 : PkgI1.iota u 1 0 = 0) (h01 : PkgI1.iota u 0 1 = 0)
    (h00 : PkgI1.iota u 0 0 = PkgI1.iota u 1 1) : u.imI = 0 ∧ u.imJ = 0 ∧ u.imK = 0 := by
  rw [iota_apply] at h10 h01 h00
  simp at h10 h01 h00
  have hs : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
  have hK : (u.imK : ℝ) = 0 := by
    have : (u.imK : ℝ) * √2 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hs.ne'
  have hJ : (u.imJ : ℝ) = 0 := by rw [hK] at h10; linarith
  have hI : (u.imI : ℝ) = 0 := by
    have : (u.imI : ℝ) * √2 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hs.ne'
  exact ⟨by exact_mod_cast hI, by exact_mod_cast hJ, by exact_mod_cast hK⟩

theorem not_sq_q (q : ℚ) (c : ℤ) (hc : ¬ IsSquare c) (h : q * q = c) : False := by
  have h1 : IsSquare (c : ℚ) := ⟨q, by rw [← h]⟩
  rw [Rat.isSquare_iff] at h1
  simp at h1
  exact hc h1

/-- **The four representatives lie in distinct cosets of `Γ¹`** (norms `1, 2, 3, 6` are distinct modulo
squares). -/
theorem coset_distinct {i j : Fin 4} (hij : i ≠ j) : (mob (g4 i))⁻¹ * mob (g4 j) ∉ Mone := by
  rintro ⟨h, ⟨w, hw, hhw, hdw⟩, hmob⟩
  set γ := (g4 i)⁻¹ * g4 j * h⁻¹ with hγ
  have hone : mob γ = 1 := by
    rw [hγ, map_mul, map_mul, map_inv, map_inv, hmob]; group
  have htriv : ∀ z : UpperHalfPlane, γ • z = z := fun z => by
    have := congrArg (fun σ : Equiv.Perm UpperHalfPlane => σ z) hone
    simpa using this
  have hn : nrd w = 1 := by
    have := hdw; rw [hhw, det_iota_eq] at this; exact_mod_cast this
  have hhinv : ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota (star w) := by
    have h1 : ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota (star w) = 1 := by
      rw [hhw, ← iota_mul, mul_star_nrd, hn]; simpa using iota_one
    have := congrArg (fun M => (((h⁻¹ : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) * M) h1
    simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, mul_one] at this
    exact this.symm
  set u := rep4i i * rep4 j * star w with hu
  have hγu : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota u := by
    rw [hγ, Units.val_mul, Units.val_mul, g4_inv_coe, hhinv, g4, coe_glOf, hu, iota_mul, iota_mul]
  have hdγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [hγu, det_iota_eq, hu, nrd_mul, nrd_mul]
    have h1 := (nd_rep j).2.2.2
    have h2 := (nd_rep i)
    have hni : nrd (rep4i i) * nrd (rep4 i) = 1 := by rw [← nrd_mul, h2.2.1]; simp [nrd]
    have hpos : 0 < nrd (rep4i i) := by
      by_contra hneg; push Not at hneg; nlinarith [h2.2.2.2]
    have hs : nrd (star w) = 1 := by simp [nrd] at hn ⊢; linarith
    rw [hs]; exact_mod_cast mul_pos (mul_pos hpos h1) one_pos
  obtain ⟨s10, s01, s00⟩ := scalar_of_trivial hdγ htriv
  rw [hγu] at s10 s01 s00
  obtain ⟨hI, hJ, hK⟩ := rat_of_scalar s10 s01 s00
  -- `nrd u = u.re²`
  have hnu : nrd u = u.re * u.re := by simp [nrd, hI, hJ, hK]; ring
  have hni : nrd (rep4i i) * nrd (rep4 i) = 1 := by rw [← nrd_mul, (nd_rep i).2.1]; simp [nrd]
  have hs : nrd (star w) = 1 := by simp [nrd] at hn ⊢; linarith
  have hprod : nrd (rep4 i) * nrd (rep4 j) = (u.re * nrd (rep4 i)) * (u.re * nrd (rep4 i)) := by
    have : nrd u = nrd (rep4i i) * nrd (rep4 j) := by rw [hu, nrd_mul, nrd_mul, hs, mul_one]
    rw [hnu] at this
    have e : nrd (rep4 j) = nrd (rep4 i) * (nrd (rep4i i) * nrd (rep4 j)) := by
      rw [← mul_assoc, mul_comm (nrd (rep4 i)), hni, one_mul]
    rw [e, ← this]; ring
  rw [nrd_rep i, nrd_rep j] at hprod
  have hsq : ∀ a b : Fin 4, a ≠ b →
      ¬ IsSquare ((![1, 2, 3, 6] : Fin 4 → ℤ) a * (![1, 2, 3, 6] : Fin 4 → ℤ) b) := by decide +kernel
  exact not_sq_q (u.re * ((![1, 2, 3, 6] : Fin 4 → ℤ) i : ℚ)) _ (hsq i j hij)
    (by push_cast; linarith)

/-- `Γ¹`-equivalence. -/
def Eq1 (a b : UpperHalfPlane) : Prop := ∃ h ∈ G1, h • a = b

theorem mob_apply (γ : GL (Fin 2) ℝ) (w : UpperHalfPlane) : mob γ w = γ • w := rfl

theorem finite_Sstar (z : UpperHalfPlane) : Finite (Sstar z) := by
  obtain ⟨h0, -⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof z
  exact Nat.finite_of_card_ne_zero (by rw [card_Sstar]; omega)

/-- **The class bound**: the representatives `i` with `g_i z` `Γ¹`-equivalent to `g_{i₀} z` inject into
`Stab*(z)/Stab¹(z)`. -/
theorem class_bound (z : UpperHalfPlane) (i₀ : Fin 4) :
    (Finset.univ.filter (fun i => Eq1 (g4 i • z) (g4 i₀ • z))).card * Nat.card (Sone z) ≤
      Nat.card (Sstar z) := by
  classical
  haveI := finite_Sstar z
  set C := Finset.univ.filter (fun i => Eq1 (g4 i • z) (g4 i₀ • z)) with hC
  have hmem : ∀ i ∈ C, ∃ h ∈ G1, h • (g4 i • z) = g4 i₀ • z := fun i hi => (Finset.mem_filter.1 hi).2
  choose hh hhG hhz using hmem
  let σ : C → Sstar z := fun i =>
    ⟨(mob (g4 i₀))⁻¹ * mob (hh i.1 i.2) * mob (g4 i.1),
      Mstar.mul_mem (Mstar.mul_mem (Mstar.inv_mem ⟨_, g4_mem i₀, rfl⟩) ⟨_, G1_le (hhG i.1 i.2), rfl⟩)
        ⟨_, g4_mem i.1, rfl⟩, by
        change ((mob (g4 i₀))⁻¹ * mob (hh i.1 i.2) * mob (g4 i.1)) z = z
        simp only [Equiv.Perm.coe_mul, Function.comp, mob_apply]
        rw [hhz i.1 i.2]
        simp⟩
  let q : Sstar z → Sstar z ⧸ (Sone z).subgroupOf (Sstar z) := QuotientGroup.mk
  have hinj : Function.Injective (q ∘ σ) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Function.comp, q] at hij
    rw [QuotientGroup.eq] at hij
    have hk : ((σ ⟨i, hi⟩)⁻¹ * σ ⟨j, hj⟩ : Sstar z).1 ∈ Mone := (Subgroup.mem_subgroupOf.1 hij).1
    simp only [σ, Subgroup.coe_mul, Subgroup.coe_inv] at hk
    set k := (mob (hh i hi))⁻¹ * mob (hh j hj)
    have hkM : k ∈ Mone := Mone.mul_mem (Mone.inv_mem ⟨_, hhG i hi, rfl⟩) ⟨_, hhG j hj, rfl⟩
    have e1 : ((mob (g4 i₀))⁻¹ * mob (hh i hi) * mob (g4 i))⁻¹ *
        ((mob (g4 i₀))⁻¹ * mob (hh j hj) * mob (g4 j)) = (mob (g4 i))⁻¹ * k * mob (g4 j) := by
      simp only [k]; group
    rw [e1] at hk
    have hi' : (mob (g4 i))⁻¹ ∈ Mstar := Mstar.inv_mem ⟨_, g4_mem i, rfl⟩
    have h2 := Mone_normal hi' (Mone.inv_mem hkM)
    have e2 : (mob (g4 i))⁻¹ * mob (g4 j) =
        ((mob (g4 i))⁻¹ * k⁻¹ * (mob (g4 i))⁻¹⁻¹) * ((mob (g4 i))⁻¹ * k * mob (g4 j)) := by group
    have h3 : (mob (g4 i))⁻¹ * mob (g4 j) ∈ Mone := by rw [e2]; exact Mone.mul_mem h2 hk
    by_contra hne
    exact coset_distinct (fun h => hne (Subtype.ext h)) h3
  have hc1 : C.card ≤ Nat.card (Sstar z ⧸ (Sone z).subgroupOf (Sstar z)) := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hL := Subgroup.card_mul_index ((Sone z).subgroupOf (Sstar z))
  have hS : Nat.card ((Sone z).subgroupOf (Sstar z)) = Nat.card (Sone z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Sone_le z)).toEquiv
  rw [hS] at hL
  rw [← hL, Subgroup.index, mul_comm (Nat.card (Sone z))]
  exact Nat.mul_le_mul_right _ hc1

/-! #### Orders along orbits -/

theorem eq_at_of_punctured_real {f g : ℂ → ℝ} {P : ℂ} (hf : ContinuousAt f P) (hg : ContinuousAt g P)
    (h : f =ᶠ[𝓝[≠] P] g) : f P = g P :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

/-- Orders agree when the moduli differ by a continuous positive factor. -/
theorem ord_eq_of_norm {F G : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) (hG : AnalyticAt ℂ G z)
    {c : ℂ → ℝ} (hc : ContinuousAt c z) (hc0 : 0 < c z) (h : ∀ᶠ w in 𝓝 z, ‖G w‖ = c w * ‖F w‖) :
    analyticOrderAt G z = analyticOrderAt F z := by
  have hcpos : ∀ᶠ w in 𝓝 z, 0 < c w := hc.eventually (lt_mem_nhds hc0)
  by_cases hFt : analyticOrderAt F z = ⊤
  · rw [hFt, analyticOrderAt_eq_top]
    rw [analyticOrderAt_eq_top] at hFt
    filter_upwards [hFt, h] with w h1 h2
    rw [h1, norm_zero, mul_zero] at h2
    exact norm_eq_zero.1 h2
  by_cases hGt : analyticOrderAt G z = ⊤
  · exfalso; apply hFt
    rw [analyticOrderAt_eq_top] at hGt ⊢
    filter_upwards [hGt, h, hcpos] with w h1 h2 h3
    rw [h1, norm_zero] at h2
    have := (mul_eq_zero.1 h2.symm).resolve_left h3.ne'
    exact norm_eq_zero.1 this
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 hFt
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hGt
  rw [← ha, ← hb]
  obtain ⟨f, hf, hf0, hfF⟩ := hF.analyticOrderAt_eq_natCast.1 hb.symm
  obtain ⟨g, hg, hg0, hgG⟩ := hG.analyticOrderAt_eq_natCast.1 ha.symm
  have key : ∀ᶠ w in 𝓝 z, ‖w - z‖ ^ a * ‖g w‖ = c w * (‖w - z‖ ^ b * ‖f w‖) := by
    filter_upwards [h, hfF, hgG] with w h1 h2 h3
    rw [h3, h2, norm_smul, norm_smul, norm_pow, norm_pow] at h1
    exact h1
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    have hev : (fun w => ‖g w‖) =ᶠ[𝓝[≠] z] (fun w => c w * (‖w - z‖ ^ (b - a) * ‖f w‖)) := by
      filter_upwards [nhdsWithin_le_nhds key, self_mem_nhdsWithin] with w h1 h2
      have hw : 0 < ‖w - z‖ ^ a := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 h2)) a
      have e : ‖w - z‖ ^ b = ‖w - z‖ ^ a * ‖w - z‖ ^ (b - a) := by
        rw [← pow_add]; congr 1; omega
      rw [e] at h1
      apply mul_left_cancel₀ hw.ne'
      linear_combination h1
    have := eq_at_of_punctured_real (hg.continuousAt.norm)
      (hc.mul ((((continuous_id.sub continuous_const).norm.pow _).continuousAt).mul hf.continuousAt.norm)) hev
    have this' : ‖g z‖ = c z * (‖z - z‖ ^ (b - a) * ‖f z‖) := this
    rw [sub_self, norm_zero, zero_pow (by omega), zero_mul, mul_zero] at this'
    have this := this'
    exact hg0 (norm_eq_zero.1 this)
  · rw [hab]
  · exfalso
    have hev : (fun w => ‖w - z‖ ^ (a - b) * ‖g w‖) =ᶠ[𝓝[≠] z] (fun w => c w * ‖f w‖) := by
      filter_upwards [nhdsWithin_le_nhds key, self_mem_nhdsWithin] with w h1 h2
      have hw : 0 < ‖w - z‖ ^ b := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 h2)) b
      have e : ‖w - z‖ ^ a = ‖w - z‖ ^ b * ‖w - z‖ ^ (a - b) := by
        rw [← pow_add]; congr 1; omega
      rw [e] at h1
      apply mul_left_cancel₀ hw.ne'
      linear_combination h1
    have := eq_at_of_punctured_real
      ((((continuous_id.sub continuous_const).norm.pow _).continuousAt).mul hg.continuousAt.norm)
      (hc.mul hf.continuousAt.norm) hev
    have this' : ‖z - z‖ ^ (a - b) * ‖g z‖ = c z * ‖f z‖ := this
    rw [sub_self, norm_zero, zero_pow (by omega), zero_mul] at this'
    have this := this'
    have := (mul_eq_zero.1 this.symm).resolve_left hc0.ne'
    exact hf0 (norm_eq_zero.1 this)

theorem Mb_analytic (γ : GL (Fin 2) ℝ) (z : UpperHalfPlane) : AnalyticAt ℂ (Mb γ) (z : ℂ) := by
  unfold Mb
  apply AnalyticAt.div (by fun_prop) (by unfold dC; fun_prop)
  rw [dC_coe]; exact denom_ne_zero γ z

theorem ord_comp_Mb {F : ℂ → ℂ} {γ : GL (Fin 2) ℝ} (z : UpperHalfPlane)
    (hF : AnalyticAt ℂ F (Mb γ z)) :
    analyticOrderAt (fun w => F (Mb γ w)) (z : ℂ) = analyticOrderAt F (Mb γ z) := by
  have hMb := Mb_analytic γ z
  have hcomp : AnalyticAt ℂ (fun w => F (Mb γ w)) z := hF.comp hMb
  have hdz : dC γ z ≠ 0 := by rw [dC_coe]; exact denom_ne_zero γ z
  have hMt : Tendsto (Mb γ) (𝓝 (z : ℂ)) (𝓝 (Mb γ z)) := hMb.continuousAt.tendsto
  by_cases ht : analyticOrderAt F (Mb γ z) = ⊤
  · rw [ht, analyticOrderAt_eq_top]
    rw [analyticOrderAt_eq_top] at ht
    exact hMt.eventually ht
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 ht
    rw [← hn]
    obtain ⟨f, hf, hf0, hfF⟩ := hF.analyticOrderAt_eq_natCast.1 hn.symm
    rw [hcomp.analyticOrderAt_eq_natCast]
    have hdet : (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast γ.isUnit.map (Matrix.detMonoidHom) |>.ne_zero
    refine ⟨fun w => ((((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) / (dC γ w * dC γ z)) ^ n *
      f (Mb γ w), ?_, ?_, ?_⟩
    · exact ((analyticAt_const.div ((by unfold dC; fun_prop : AnalyticAt ℂ (dC γ) (z : ℂ)).mul
        analyticAt_const) (mul_ne_zero hdz hdz)).pow n).mul (hf.comp hMb)
    · exact mul_ne_zero (pow_ne_zero _ (div_ne_zero hdet (mul_ne_zero hdz hdz))) hf0
    · filter_upwards [hMt.eventually hfF, (dC_cont γ).continuousAt.eventually_ne hdz] with w h1 h2
      rw [h1, Mb_sub γ h2 hdz, smul_eq_mul, smul_eq_mul,
        show (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) * (w - (z : ℂ)) / (dC γ w * dC γ (z : ℂ)) =
          (w - (z : ℂ)) * ((((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) / (dC γ w * dC γ (z : ℂ))) by ring,
        mul_pow]
      ring

/-- **Orders are constant along `Γ*`-orbits** (from the automorphy in absolute value). -/
theorem ord_smul_eq {m : ℕ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    (haut : ∀ γ ∈ Γs, ∀ w : UpperHalfPlane,
      ‖F ((γ • w : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ w‖ ^ (2 * m) * ‖F (w : ℂ)‖) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) (z : UpperHalfPlane) :
    analyticOrderAt F ((γ • z : UpperHalfPlane) : ℂ) = analyticOrderAt F (z : ℂ) := by
  have hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det := by obtain ⟨_, _, _, hd⟩ := hγ; exact hd
  have hFγ : AnalyticAt ℂ F (Mb γ z) := by rw [Mb_coe hd]; exact hF _ (γ • z).im_pos
  rw [← Mb_coe hd z, ← ord_comp_Mb z hFγ]
  have hdz : dC γ z ≠ 0 := by rw [dC_coe]; exact denom_ne_zero γ z
  refine ord_eq_of_norm (hF _ z.im_pos) (hFγ.comp (Mb_analytic γ z))
    (c := fun w => ‖dC γ w‖ ^ (2 * m) / ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m) ?_ ?_ ?_
  · exact (((dC_cont γ).continuousAt.norm.pow _).div continuousAt_const (pow_pos hd m).ne')
  · exact div_pos (pow_pos (norm_pos_iff.2 hdz) _) (pow_pos hd m)
  · filter_upwards [isOpen_U.mem_nhds z.im_pos] with w hw
    have e := haut γ hγ ⟨w, hw⟩
    rw [← Mb_coe hd, ← dC_coe] at e
    simp only [UpperHalfPlane.coe_mk] at e ⊢
    field_simp
    linarith

end Index

include hT hV hC in
/-- **Row H-88 from published leaves and project glue**: the valence formula, Shimizu's volume formula, the
glue from `𝒪¹` to `Γ*`, the CM value (and the bundle leaf `r4`). -/
theorem qmHauptmodulBase3_of_shimizu (hS : ShimizuCovolumeO1) (hG : GammaStarFromO1) :
    QMHauptmodulBase3 :=
  qmHauptmodulBase3_of' hT hV (hG hS) hC

end

end HDec.LeafQCheck.HM.QMSplit
