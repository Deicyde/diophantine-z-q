import TailK

/-!
# qm-split, row H-87: `ValenceFormulaGammaStar` split

The row (leafq-check `scratch/leafq-check/Fold.lean` l.487 @ w54, namespace `HDec.LeafQCheck.VB`; not in the
chain, so `ellOrder` and the row are copied verbatim below, with the same `open`s) is the valence formula for
`Γ*` with the volume of `Γ*\ℍ` already inserted. Split:

* **LEAF `ValenceFormulaCocompact`** (published form): the valence formula for any cocompact Fuchsian group
  `Γ ⊆ GL₂(ℝ)⁺` acting on `ℍ`, `Σ_{P ∈ T} ord_P(F)/e_P ≤ k·vol(Γ\ℍ)/(4π)` for weight `k = 2m`, with the volume
  the hyperbolic area (Mathlib's invariant measure `dx dy/y²` on `ℍ`) of a fundamental domain;
* **GLUE `GammaStarCocompactArea`**: `Γ*` acts as a cocompact Fuchsian group with a fundamental domain of
  area `π/6`.

`valenceFormulaGammaStar_of` proves the row: `(2m/4π)·(π/6) = m/12`.

Check: `scratch/qm-split/chk.sh scratch/qm-split/Valence.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.LeafQCheck

open PkgI1

namespace QMSplitVB

open HSyn.G0Split.FibreQM.PeriodMap (U ValenceBoundGammaStar)
open UpperHalfPlane (num denom denom_ne_zero)

open scoped ENNReal

/-! ## The row, copied verbatim (leafq-check `Fold.lean` l.466-497) -/

/-- **`e_P`**: the order of the stabilizer of `P` in `Γ*/ℚ^×`, counted as the number of distinct Möbius
maps `z ↦ γ • z` with `γ ∈ Γ*`, `γ • P = P` (the image of `Γ*` in `PSL₂(ℝ)` acts faithfully on `ℍ`; the
rational scalars act trivially). `Nat.card` is `0` if the stabilizer were infinite. -/
noncomputable def ellOrder (P : UpperHalfPlane) : ℕ :=
  Nat.card {f : UpperHalfPlane → UpperHalfPlane //
    ∃ γ ∈ PkgI1.GammaStar, γ • P = P ∧ f = fun z => γ • z}

/-- **LEAF (the valence formula for `Γ*`, inequality form over a finite set of inequivalent points).**
For `F` holomorphic on `ℍ`, not identically zero, with `|F(γτ)| det(γ)^m = |cτ+d|^{2m}|F(τ)|` for all
`γ ∈ Γ*` (weight `k = 2m`, unitary multiplier), and every finite set `T` of pairwise `Γ*`-inequivalent
points: `Σ_{P ∈ T} ord_P(F)/e_P ≤ m/12`.

Published form: for a Fuchsian group `Γ` of the first kind without cusps and `F ≠ 0` an automorphic form of
weight `k` (unitary multiplier), `Σ_{P ∈ Γ\ℍ} ord_P(F)/e_P = (k/4π)·vol(Γ\ℍ) = (k/2)(2g − 2 + Σ_j(1 − 1/e_j))`
(Shimura, *Introduction to the arithmetic theory of automorphic functions*, 1971, Prop. 2.16 and
Thm. 2.20 / formula (2.4.x); Rankin, *Modular forms and functions*, 1977, Thm. 4.1.4 for arbitrary
unitary multiplier systems; theorem numbers UNVERIFIED), with the signature `(0; 2, 4, 6)` of
`Γ*/ℚ^× = N_B(𝒪)⁺/ℚ^×` for the quaternion algebra of discriminant 6 (Takeuchi, J. Fac. Sci. Univ. Tokyo
24 (1977), the arithmetic triangle group `(2,4,6)`; Elkies, ANTS-III (1998) §3; locators UNVERIFIED), so the
right side is `m·(−2 + 1/2 + 3/4 + 5/6) = m/12`. Dropping the points outside `T` (all terms are `≥ 0`)
gives the inequality. A consequence of the published statements. -/
def ValenceFormulaGammaStar : Prop :=
  ∀ (m : ℕ) (F : ℂ → ℂ), AnalyticOnNhd ℂ F U → (∃ z ∈ U, F z ≠ 0) →
    (∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) →
    ∀ T : Finset UpperHalfPlane,
      (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ PkgI1.GammaStar, γ • z ≠ w) →
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrder z : ℝ≥0∞) ≤ (m : ℝ≥0∞) / 12

/-! ## Genuine definitions for a general group `Γ ⊆ GL₂(ℝ)` acting on `ℍ` -/

/-- `e_P` for a general `Γ`: the number of distinct Möbius maps of elements of `Γ` fixing `P`. -/
noncomputable def ellOrderOf (Γ : Set (GL (Fin 2) ℝ)) (P : UpperHalfPlane) : ℕ :=
  Nat.card {f : UpperHalfPlane → UpperHalfPlane // ∃ γ ∈ Γ, γ • P = P ∧ f = fun z => γ • z}

theorem ellOrderOf_gammaStar : ellOrderOf PkgI1.GammaStar = ellOrder := rfl

/-- **`Γ` acts on `ℍ` as a cocompact Fuchsian group**: a group of matrices of positive determinant whose
Möbius action is properly discontinuous (only finitely many Möbius maps of `Γ` move a compact set to meet
itself) with a compact set meeting every orbit. (Scalars are allowed in `Γ`: they act trivially.) -/
structure IsCocompactFuchsian (Γ : Set (GL (Fin 2) ℝ)) : Prop where
  one_mem : 1 ∈ Γ
  mul_mem : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ
  inv_mem : ∀ a ∈ Γ, a⁻¹ ∈ Γ
  det_pos : ∀ a ∈ Γ, 0 < (a : Matrix (Fin 2) (Fin 2) ℝ).det
  properlyDiscontinuous : ∀ K : Set UpperHalfPlane, IsCompact K →
    {f : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ, f = (fun z => γ • z) ∧ (f '' K ∩ K).Nonempty}.Finite
  cocompact : ∃ C : Set UpperHalfPlane, IsCompact C ∧ ∀ z, ∃ γ ∈ Γ, γ • z ∈ C

/-- **A fundamental domain of `Γ` on `ℍ`**: measurable, meets every orbit, and almost disjoint from its
translates by the Möbius maps of `Γ` other than the identity (measure: Mathlib's `GL(2, ℝ)`-invariant
measure `dx dy / y²` on `ℍ`, `UpperHalfPlane.volume_def`). -/
def IsFundDomain (Γ : Set (GL (Fin 2) ℝ)) (s : Set UpperHalfPlane) : Prop :=
  MeasurableSet s ∧ (∀ z, ∃ γ ∈ Γ, γ • z ∈ s) ∧
    ∀ γ ∈ Γ, (fun z : UpperHalfPlane => γ • z) ≠ id →
      MeasureTheory.volume (s ∩ (fun z : UpperHalfPlane => γ • z) ⁻¹' s) = 0

/-! ## The leaf and the glue -/

/-- **LEAF (the valence formula for a cocompact Fuchsian group).** Let `Γ ⊆ GL₂(ℝ)⁺` act on `ℍ` as a
cocompact Fuchsian group, `s` a fundamental domain, `F` holomorphic on `ℍ`, not identically zero, with
`|F(γτ)| det(γ)^m = |cτ + d|^{2m} |F(τ)|` for `γ ∈ Γ` (weight `k = 2m`, a unitary multiplier system). Then for
every finite set `T` of pairwise `Γ`-inequivalent points, `Σ_{P ∈ T} ord_P(F)/e_P ≤ k·vol(s)/(4π)`.

Published form: for a Fuchsian group of the first kind with compact quotient and a nonzero automorphic form
of weight `k` (any unitary multiplier), `Σ_{P ∈ Γ\ℍ} ord_P(F)/e_P = k·vol(Γ\ℍ)/(4π)` (Shimura, *Introduction
to the arithmetic theory of automorphic functions*, 1971, Prop. 2.16 and Thm. 2.20 with (2.4.x); Rankin,
*Modular forms and functions*, 1977, Thm. 4.1.4 for unitary multiplier systems; theorem numbers UNVERIFIED,
no network). The inequality over a finite `T` drops nonnegative terms of the printed sum. -/
def ValenceFormulaCocompact : Prop :=
  ∀ (Γ : Set (GL (Fin 2) ℝ)), IsCocompactFuchsian Γ → ∀ s, IsFundDomain Γ s →
  ∀ (m : ℕ) (F : ℂ → ℂ), AnalyticOnNhd ℂ F U → (∃ z ∈ U, F z ≠ 0) →
    (∀ γ ∈ Γ, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) →
    ∀ T : Finset UpperHalfPlane,
      (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w) →
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrderOf Γ z : ℝ≥0∞) ≤
        (2 * m : ℝ≥0∞) * MeasureTheory.volume s / ENNReal.ofReal (4 * Real.pi)

/-- **GLUE (`Γ*` is a cocompact Fuchsian group with covolume `π/6`).** `Γ* = ι(N_B(𝒪)⁺)` acts on `ℍ` as a
cocompact Fuchsian group and has a fundamental domain of hyperbolic area `π/6`.

What it needs (published; locators UNVERIFIED): `𝒪¹` (norm-one units of the maximal order of the indefinite
division algebra `B`) is a cocompact Fuchsian group (Shimura 1971, §9.2, Prop. 9.2 / Thm. 9.3); Shimizu's
volume formula `vol(𝒪¹\ℍ) = (π/3) ∏_{p | 6} (p − 1) = 2π/3` (Shimizu, Ann. of Math. 81 (1965); Vignéras,
*Arithmétique des algèbres de quaternions*, IV §1; Voight, *Quaternion algebras*, Thm. 39.1.13); the index
`[Γ* : ℚ^× 𝒪¹] = 4` modulo scalars (`N_B(𝒪)⁺/ℚ^×𝒪¹ ≅ W ≅ (ℤ/2)²`, the Atkin–Lehner group; the chain's
`tt` representatives and pkg-I1's `x4`, `x6`); and the comparison of fundamental domains under a subgroup of
finite index. Equivalently: `Γ*/ℚ^×` is the triangle group `(2, 4, 6)` (Takeuchi, J. Fac. Sci. Univ. Tokyo 24
(1977)) and Gauss–Bonnet gives area `2(π − π/2 − π/4 − π/6) = π/6`. -/
def GammaStarCocompactArea : Prop :=
  IsCocompactFuchsian PkgI1.GammaStar ∧
    ∃ s, IsFundDomain PkgI1.GammaStar s ∧ MeasureTheory.volume s = ENNReal.ofReal (Real.pi / 6)

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

/-- **Row H-87 from the leaf and the glue.** -/
theorem valenceFormulaGammaStar_of (hV : ValenceFormulaCocompact) (hG : GammaStarCocompactArea) :
    ValenceFormulaGammaStar := by
  intro m F hF hne haut T hT
  obtain ⟨hFuchs, s, hs, hvol⟩ := hG
  have := hV PkgI1.GammaStar hFuchs s hs m F hF hne haut T hT
  rw [hvol, arith] at this
  exact this


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

/-- **Row H-87 from the published leaves and the project glue.** -/
theorem valenceFormulaGammaStar_of_shimizu (hV : ValenceFormulaCocompact) (hS : ShimizuCovolumeO1)
    (hG : GammaStarFromO1) : ValenceFormulaGammaStar :=
  valenceFormulaGammaStar_of hV (hG hS)

end QMSplitVB

end HDec.LeafQCheck

#print axioms HDec.LeafQCheck.QMSplitVB.valenceFormulaGammaStar_of
#print axioms HDec.LeafQCheck.QMSplitVB.valenceFormulaGammaStar_of_shimizu
