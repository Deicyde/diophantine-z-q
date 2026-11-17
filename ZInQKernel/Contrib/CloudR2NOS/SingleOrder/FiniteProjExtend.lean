/-
# H5 / NOS round 2, lane 1: extension of chart sections to high Source tensor powers (Stacks 01PW route)

Newly authored glue (H5 round-2 lane 1, 2026-11-15), additive to cp9–cp11. Inputs read-only: the canonical
Source port (LITERAL `ProjPresentation`, `tensorPow`, `tensorPowSection`, frames; FLT @ 6e837e75…, Apache-2.0,
Anthropic, PBC), W07 (`Proj.mem_basicOpen_iff_isUnit_val`; Jacobian-Challenge @ c4254cce…, Apache-2.0) and
Mathlib (`exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated`,
`exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact`, sheaf gluing).

This file first proves the chart geometry: inside the chart of `X_j`, the chart of `X_i` is exactly the
basic open of the pulled-back ratio `X_i / X_j`.
-/
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.FiniteProjPowerTensor
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.FiniteProjClosed

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower

section ChartGeometry

variable {R : Type u} [CommRing R] {N : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

/-- A point of `D₊(X_j)` lies in the basic open of the ratio `X_i / X_j` iff it lies in `D₊(X_i)`. -/
theorem mem_basicOpen_ratio_iff (i j : Fin (N + 1)) (x : Proj 𝒜)
    (hx : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j)) :
    x ∈ (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 (MvPolynomial.X j)
        (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio R N j i)) ↔
      x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X i) := by
  rw [Proj.mem_basicOpen_iff_isUnit_val _ hx]
  have h3 := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 (MvPolynomial.X j)
    (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio R N j i) ⟨x, hx⟩
  haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  change IsUnit (((ProjectiveSpectrum.Proj.awayToSection 𝒜 (MvPolynomial.X j)).1
    (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio R N j i)).val ⟨x, hx⟩).val ↔ _
  rw [h3]
  simp only [ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    RingHom.id_apply]
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

/-- Inside `D₊(X_j)`, the basic open of `X_i / X_j` is `D₊(X_j) ⊓ D₊(X_i)`. -/
theorem basicOpen_ratio (i j : Fin (N + 1)) :
    (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 (MvPolynomial.X j)
        (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio R N j i)) =
      Proj.basicOpen 𝒜 (MvPolynomial.X j) ⊓ Proj.basicOpen 𝒜 (MvPolynomial.X i) := by
  ext x
  constructor
  · intro h
    have hx : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j) := (Proj 𝒜).basicOpen_le _ h
    exact ⟨hx, (mem_basicOpen_ratio_iff i j x hx).mp h⟩
  · rintro ⟨hx, hi⟩
    exact (mem_basicOpen_ratio_iff i j x hx).mpr hi

variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules}
  (𝔓 : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation M f N)

/-- **K1.** Inside the chart of `X_j`, the chart of `X_i` is the basic open of the pulled-back ratio. -/
theorem basicOpen_chartRatio (i j : Fin (N + 1)) :
    X.basicOpen (chartRatio 𝔓 j i) = chart 𝔓 j ⊓ chart 𝔓 i := by
  rw [chartRatio, ← Scheme.preimage_basicOpen, basicOpen_ratio]
  rfl

end ChartGeometry

section Extension

variable {R : Type u} [CommRing R] {N : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules}
  (𝔓 : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation M f N)

local notation "TP" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M

/-- Sections over `U` are determined by their restrictions to an open `D` equal to `U`. -/
theorem eq_of_map_eq_of_eq {L : X.Modules} {D U : X.Opens} (hDU : D ≤ U) (h : D = U) {a c : Γ(L, U)}
    (hac : L.presheaf.map (homOfLE hDU).op a = L.presheaf.map (homOfLE hDU).op c) : a = c := by
  subst h
  have e : homOfLE hDU = 𝟙 D := Subsingleton.elim _ _
  rw [e] at hac
  simpa using hac

/-- The Source ratio equation restricted to any `W` inside the chart of `X_a`. -/
theorem chartRatio_smul (a c : Fin (N + 1)) {W : X.Opens} (h : W ≤ chart 𝔓 a) :
    X.presheaf.map (homOfLE h).op (chartRatio 𝔓 a c) • M.presheaf.map (homOfLE h).op (chartSigma 𝔓 a) =
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (𝔓.σ c) := by
  rw [← Scheme.Modules.map_smul, chartSigma, chartRatio, 𝔓.app_ratio_smul a c,
    presheaf_map_homOfLE_map_homOfLE]

/-- The multiplicative cocycle of the pulled-back ratios on a double overlap. -/
theorem chartRatio_cocycle (i j l : Fin (N + 1)) {W : X.Opens} (hj : W ≤ chart 𝔓 j)
    (hl : W ≤ chart 𝔓 l) :
    X.presheaf.map (homOfLE hj).op (chartRatio 𝔓 j i) =
      X.presheaf.map (homOfLE hl).op (chartRatio 𝔓 l i) *
        X.presheaf.map (homOfLE hj).op (chartRatio 𝔓 j l) := by
  apply ((isFrameOn_chartSigma 𝔓 j).bijective hj hj).1
  change X.presheaf.map (homOfLE hj).op (chartRatio 𝔓 j i) •
      M.presheaf.map (homOfLE hj).op (chartSigma 𝔓 j) =
    (X.presheaf.map (homOfLE hl).op (chartRatio 𝔓 l i) *
        X.presheaf.map (homOfLE hj).op (chartRatio 𝔓 j l)) •
      M.presheaf.map (homOfLE hj).op (chartSigma 𝔓 j)
  rw [mul_smul, chartRatio_smul 𝔓 j l hj, chartRatio_smul 𝔓 j i hj]
  have hσl : M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (𝔓.σ l) =
      M.presheaf.map (homOfLE hl).op (chartSigma 𝔓 l) := by
    rw [chartSigma, presheaf_map_homOfLE_map_homOfLE]
  rw [hσl, chartRatio_smul 𝔓 l i hl]

variable [IsAffineHom 𝔓.toProj]

theorem isAffineOpen_chart (j : Fin (N + 1)) : IsAffineOpen (chart 𝔓 j) :=
  (Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X j) (X_mem_one (R := R) (N := N) j)
    Nat.one_pos).preimage 𝔓.toProj

theorem isCompact_chart_inf (j l : Fin (N + 1)) :
    IsCompact ((chart 𝔓 j ⊓ chart 𝔓 l : X.Opens) : Set X) := by
  have hm : MvPolynomial.X j * MvPolynomial.X l ∈ 𝒜 2 :=
    SetLike.mul_mem_graded (X_mem_one (R := R) (N := N) j) (X_mem_one (R := R) (N := N) l)
  have e : chart 𝔓 j ⊓ chart 𝔓 l =
      𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j * MvPolynomial.X l) := by
    rw [Proj.basicOpen_mul]
    rfl
  rw [e]
  exact ((Proj.isAffineOpen_basicOpen 𝒜 _ hm two_pos).preimage 𝔓.toProj).isCompact

variable (i : Fin (N + 1)) (b : Γ(X, chart 𝔓 i))

theorem basicOpen_le_chart (j : Fin (N + 1)) : X.basicOpen (chartRatio 𝔓 j i) ≤ chart 𝔓 i := by
  rw [basicOpen_chartRatio]
  exact inf_le_right

/-- Mathlib's clearing of denominators for FUNCTIONS on the affine chart of `X_j`. -/
theorem exists_lift (j : Fin (N + 1)) : ∃ (n : ℕ) (y : Γ(X, chart 𝔓 j)),
    X.presheaf.map (homOfLE (X.basicOpen_le (chartRatio 𝔓 j i))).op y =
      (X.presheaf.map (homOfLE (X.basicOpen_le (chartRatio 𝔓 j i))).op (chartRatio 𝔓 j i)) ^ n *
        X.presheaf.map (homOfLE (basicOpen_le_chart 𝔓 i j)).op b :=
  exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X (chart 𝔓 j) (isAffineOpen_chart 𝔓 j).isCompact
    (isAffineOpen_chart 𝔓 j).isQuasiSeparated (chartRatio 𝔓 j i)
    (X.presheaf.map (homOfLE (basicOpen_le_chart 𝔓 i j)).op b)

/-- The local candidate on the chart of `X_j`, at level `m`. -/
def localExt (j : Fin (N + 1)) (n : ℕ) (y : Γ(X, chart 𝔓 j)) (m : ℕ) : Γ(TP m, chart 𝔓 j) :=
  (y * chartRatio 𝔓 j i ^ (m - n)) • chartSigmaPow 𝔓 j m

/-- On `W ⊆ chart_j ∩ chart_i`, the local candidate is `b • σ_iᵐ`. -/
theorem localExt_restrict (j : Fin (N + 1)) (n : ℕ) (y : Γ(X, chart 𝔓 j))
    (hy : X.presheaf.map (homOfLE (X.basicOpen_le (chartRatio 𝔓 j i))).op y =
      (X.presheaf.map (homOfLE (X.basicOpen_le (chartRatio 𝔓 j i))).op (chartRatio 𝔓 j i)) ^ n *
        X.presheaf.map (homOfLE (basicOpen_le_chart 𝔓 i j)).op b)
    (m : ℕ) (hm : n ≤ m) {W : X.Opens} (hWj : W ≤ chart 𝔓 j) (hWi : W ≤ chart 𝔓 i) :
    (TP m).presheaf.map (homOfLE hWj).op (localExt 𝔓 i j n y m) =
      X.presheaf.map (homOfLE hWi).op b • (TP m).presheaf.map (homOfLE hWi).op (chartSigmaPow 𝔓 i m) := by
  have hWD : W ≤ X.basicOpen (chartRatio 𝔓 j i) := by
    rw [basicOpen_chartRatio]
    exact le_inf hWj hWi
  rw [localExt, Scheme.Modules.map_smul, chartSigmaPow_rel 𝔓 j i m hWj hWi, smul_smul]
  congr 1
  have hy' := congrArg (X.presheaf.map (homOfLE hWD).op) hy
  rw [map_mul, map_pow, presheaf_map_map, presheaf_map_map, presheaf_map_map] at hy'
  rw [map_mul, map_pow, hy']
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_sub_cancel_left]
  ring


/-- On a double overlap, the level-`m₀` discrepancy of two local candidates is killed by a power of
the ratio of `X_i` (Mathlib's compact-open vanishing). -/
theorem exists_kill (j l : Fin (N + 1)) (nj nl : ℕ) (yj : Γ(X, chart 𝔓 j)) (yl : Γ(X, chart 𝔓 l))
    (hyj : X.presheaf.map (homOfLE (X.basicOpen_le (chartRatio 𝔓 j i))).op yj =
      (X.presheaf.map (homOfLE (X.basicOpen_le (chartRatio 𝔓 j i))).op (chartRatio 𝔓 j i)) ^ nj *
        X.presheaf.map (homOfLE (basicOpen_le_chart 𝔓 i j)).op b)
    (hyl : X.presheaf.map (homOfLE (X.basicOpen_le (chartRatio 𝔓 l i))).op yl =
      (X.presheaf.map (homOfLE (X.basicOpen_le (chartRatio 𝔓 l i))).op (chartRatio 𝔓 l i)) ^ nl *
        X.presheaf.map (homOfLE (basicOpen_le_chart 𝔓 i l)).op b)
    (m₀ : ℕ) (hj : nj ≤ m₀) (hl : nl ≤ m₀) :
    ∃ k : ℕ, (X.presheaf.map (homOfLE (inf_le_left : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 j)).op
        (chartRatio 𝔓 j i)) ^ k *
      (X.presheaf.map (homOfLE (inf_le_left : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 j)).op
          (yj * chartRatio 𝔓 j i ^ (m₀ - nj)) -
        X.presheaf.map (homOfLE (inf_le_right : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 l)).op
          (yl * chartRatio 𝔓 l i ^ (m₀ - nl)) *
        (X.presheaf.map (homOfLE (inf_le_left : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 j)).op
          (chartRatio 𝔓 j l)) ^ m₀) = 0 := by
  set ρ := X.presheaf.map (homOfLE (inf_le_left : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 j)).op
    (chartRatio 𝔓 j i) with hρ
  refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X (isCompact_chart_inf 𝔓 j l) _ ρ ?_
  have hW'W : X.basicOpen ρ ≤ chart 𝔓 j ⊓ chart 𝔓 l := X.basicOpen_le ρ
  have hW'i : X.basicOpen ρ ≤ chart 𝔓 i := by
    rw [hρ, Scheme.basicOpen_res]
    exact inf_le_right.trans (basicOpen_le_chart 𝔓 i j)
  have hj' : X.basicOpen ρ ≤ chart 𝔓 j := hW'W.trans inf_le_left
  have hl' : X.basicOpen ρ ≤ chart 𝔓 l := hW'W.trans inf_le_right
  have ej := localExt_restrict 𝔓 i b j nj yj hyj m₀ hj hj' hW'i
  have el := localExt_restrict 𝔓 i b l nl yl hyl m₀ hl hl' hW'i
  rw [localExt, Scheme.Modules.map_smul] at ej
  rw [localExt, Scheme.Modules.map_smul, chartSigmaPow_rel 𝔓 j l m₀ hj' hl', smul_smul] at el
  have key := (((isFrameOn_chartSigma 𝔓 j).tensorPowSection m₀).bijective hj' hj').1 (ej.trans el.symm)
  change X.presheaf.map (homOfLE hj').op (yj * chartRatio 𝔓 j i ^ (m₀ - nj)) =
    X.presheaf.map (homOfLE hl').op (yl * chartRatio 𝔓 l i ^ (m₀ - nl)) *
      X.presheaf.map (homOfLE hj').op (chartRatio 𝔓 j l) ^ m₀ at key
  change X.presheaf.map (homOfLE (X.basicOpen_le ρ)).op (_ - _ * _) = 0
  rw [map_sub, sub_eq_zero]
  simp only [map_mul, map_pow, presheaf_map_map] at key ⊢
  exact key

/-- At every level `m ≥ m₀` beyond the killing exponent, two local candidates agree on the overlap. -/
theorem localExt_compat (j l : Fin (N + 1)) (nj nl : ℕ) (yj : Γ(X, chart 𝔓 j)) (yl : Γ(X, chart 𝔓 l))
    (m₀ k m : ℕ) (hj : nj ≤ m₀) (hl : nl ≤ m₀) (hm : m₀ + k ≤ m)
    (hk : (X.presheaf.map (homOfLE (inf_le_left : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 j)).op
        (chartRatio 𝔓 j i)) ^ k *
      (X.presheaf.map (homOfLE (inf_le_left : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 j)).op
          (yj * chartRatio 𝔓 j i ^ (m₀ - nj)) -
        X.presheaf.map (homOfLE (inf_le_right : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 l)).op
          (yl * chartRatio 𝔓 l i ^ (m₀ - nl)) *
        (X.presheaf.map (homOfLE (inf_le_left : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 j)).op
          (chartRatio 𝔓 j l)) ^ m₀) = 0) :
    (TP m).presheaf.map (homOfLE (inf_le_left : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 j)).op
        (localExt 𝔓 i j nj yj m) =
      (TP m).presheaf.map (homOfLE (inf_le_right : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 l)).op
        (localExt 𝔓 i l nl yl m) := by
  rw [localExt, localExt, Scheme.Modules.map_smul, Scheme.Modules.map_smul,
    chartSigmaPow_rel 𝔓 j l m inf_le_left inf_le_right, smul_smul]
  congr 1
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hcoc := chartRatio_cocycle 𝔓 i j l (inf_le_left : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 j) inf_le_right
  have h1 : m₀ + k + e - nj = (m₀ - nj) + (k + e) := by omega
  have h2 : m₀ + k + e - nl = (m₀ - nl) + (k + e) := by omega
  rw [h1, h2, show m₀ + k + e = m₀ + (k + e) by omega]
  simp only [map_mul, map_pow] at hk ⊢
  rw [hcoc] at hk ⊢
  linear_combination ((X.presheaf.map (homOfLE (inf_le_right : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 l)).op
      (chartRatio 𝔓 l i) * X.presheaf.map (homOfLE (inf_le_left : chart 𝔓 j ⊓ chart 𝔓 l ≤ chart 𝔓 j)).op
      (chartRatio 𝔓 j l)) ^ e) * hk

/-- **Corner C (extension, Stacks 01PW for the literal Source tensor powers).** For an ACTUAL
presentation with affine `toProj` (e.g. finite), every function on the chart of `X_i` times `σ_iᵐ`
extends to a GLOBAL section of `M.tensorPow m`, for all sufficiently large `m`. -/
theorem exists_extension :
    ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∃ t : Γ(TP m, ⊤),
      (TP m).presheaf.map (homOfLE (le_top : chart 𝔓 i ≤ ⊤)).op t = b • chartSigmaPow 𝔓 i m := by
  classical
  choose n y hy using exists_lift 𝔓 i b
  set m₀ := Finset.univ.sup n with hm₀
  have hn : ∀ j, n j ≤ m₀ := fun j => Finset.le_sup (Finset.mem_univ j)
  choose k hk using fun j l => exists_kill 𝔓 i b j l (n j) (n l) (y j) (y l) (hy j) (hy l) m₀
    (hn j) (hn l)
  set K := Finset.univ.sup (fun p : Fin (N + 1) × Fin (N + 1) => k p.1 p.2) with hK
  have hkK : ∀ j l, k j l ≤ K := fun j l =>
    Finset.le_sup (f := fun p : Fin (N + 1) × Fin (N + 1) => k p.1 p.2) (Finset.mem_univ (j, l))
  refine ⟨m₀ + K, fun m hm => ?_⟩
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨(TP m).presheaf, (TP m).isSheaf⟩
  have hcover : (⊤ : X.Opens) ≤ iSup (chart 𝔓) := fun x _ =>
    TopologicalSpace.Opens.mem_iSup.mpr (chart_cover 𝔓 x)
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' F (chart 𝔓) ⊤ (fun j => homOfLE le_top) hcover
    (fun j => localExt 𝔓 i j (n j) (y j) m) (fun j l => by
      exact localExt_compat 𝔓 i j l (n j) (n l) (y j) (y l) m₀ K m (hn j) (hn l) hm (by
        rw [← Nat.sub_add_cancel (hkK j l), pow_add, mul_assoc, hk j l, mul_zero]))
  refine ⟨t, ?_⟩
  rw [ht i]
  -- on the chart of `X_i` itself, the local candidate IS `b • σ_iᵐ`
  have hD : X.basicOpen (chartRatio 𝔓 i i) = chart 𝔓 i := by
    rw [basicOpen_chartRatio, inf_idem]
  apply eq_of_map_eq_of_eq (X.basicOpen_le (chartRatio 𝔓 i i)) hD
  rw [localExt_restrict 𝔓 i b i (n i) (y i) (hy i) m ((hn i).trans (Nat.le_add_right _ _ |>.trans hm))
    (X.basicOpen_le _) (X.basicOpen_le _), Scheme.Modules.map_smul]

end Extension

end ZInQ.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower
