/-
# H5 / NOS round 2, lane 1: Source tensor powers of a ProjPresentation's line are the pulled-back 𝒪(n)

Newly authored glue (H5 round-2 lane 1, 2026-11-15), additive to cp9 (`FiniteProjPower.lean`, unchanged).
Inputs read-only: the canonical Source port (FLT @ 6e837e75…; Apache-2.0, Anthropic, PBC) — the LITERAL
`Scheme.Modules.tensorPow` (recursive `𝟙_` / `_ ⊗ L` with the Source monoidal structure), `tensorPowSection`,
`map_tensorPowSection`, `tensorPowSection_smul`, `IsFrameOn.tensorPowSection` and the iso criterion
`exists_iso_app_eq_of_isFrameOn_of_eq_smul`; and the vendored W07 contribution (Jacobian-Challenge @ c4254cce…;
Apache-2.0, Delaval/Xu/Xu) — the twisting sheaves `Proj.twist`, the power sections `Proj.twistPowSection`
(`fⁿ` on `D₊(f)`), their free-generator property and multiplicative transition rule.

Corner B (`exists_iso_pullback_twist_tensorPow`): for the ACTUAL presentation `𝔓 : M.ProjPresentation f N`
and EVERY `n : ℕ` (including `n = 0`), `𝔓.toProj^* 𝒪(n) ≅ M.tensorPow n` (literal Source power) by an
isomorphism sending the pulled-back `X_iⁿ` to `tensorPowSection σ_i n` on each chart. It is constructed from
the presentation's frames and ratio equations only; W07's monoidal structure is NOT used or identified with
the Source one — the comparison is a genuine frame-by-frame isomorphism.
-/
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.Tensor

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower

section CornerB

variable {R : Type u} [CommRing R] {N : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

/-- Naturality of a scheme morphism's pullback of functions, elementwise. -/
theorem app_map_apply {X Y : Scheme.{u}} (g : X ⟶ Y) {U U' : Y.Opens} (h : U ≤ U') (a : Γ(Y, U')) :
    g.app U (Y.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (g.preimage_mono h)).op (g.app U' a) := by
  have := congrArg (fun φ => φ.hom a) (g.naturality (homOfLE h).op)
  exact this

/-- The ratio `X_j / X_i` restricted to `D₊(X_i) ⊓ D₊(X_j)`. -/
def ratioOn (i j : Fin (N + 1)) :
    Γ(Proj 𝒜, Proj.basicOpen 𝒜 (MvPolynomial.X i) ⊓ Proj.basicOpen 𝒜 (MvPolynomial.X j)) :=
  (Proj 𝒜).presheaf.map (homOfLE inf_le_left).op
    (Proj.awayToSection 𝒜 (MvPolynomial.X i)
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio R N i j))

/-- Degree zero: `X_i⁰ = X_j⁰` on the overlap. -/
theorem twistPow_zero_rel (i j : Fin (N + 1)) :
    (Proj.twist 𝒜 0).presheaf.map
        (homOfLE (inf_le_left : Proj.basicOpen 𝒜 (MvPolynomial.X i) ⊓
          Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i))).op
        (Proj.twistPowSection 0 (X_mem_one (R := R) (N := N) i)) =
      (Proj.twist 𝒜 0).presheaf.map
        (homOfLE (inf_le_right : Proj.basicOpen 𝒜 (MvPolynomial.X i) ⊓
          Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ Proj.basicOpen 𝒜 (MvPolynomial.X j))).op
        (Proj.twistPowSection 0 (X_mem_one (R := R) (N := N) j)) := by
  refine Subtype.ext (funext fun point ↦ Subtype.ext ?_)
  exact (Proj.val_twistPowSection_zero (X_mem_one (R := R) (N := N) i)
      ⟨point.1, (inf_le_left : Proj.basicOpen 𝒜 (MvPolynomial.X i) ⊓
        Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ _) point.2⟩).trans
    (Proj.val_twistPowSection_zero (X_mem_one (R := R) (N := N) j)
      ⟨point.1, (inf_le_right : Proj.basicOpen 𝒜 (MvPolynomial.X i) ⊓
        Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ _) point.2⟩).symm

/-- Degree one: `(X_j / X_i) • X_i = X_j` on the overlap. -/
theorem twistPow_one_rel (i j : Fin (N + 1)) :
    ratioOn (R := R) i j • (Proj.twist 𝒜 1).presheaf.map
        (homOfLE (inf_le_left : Proj.basicOpen 𝒜 (MvPolynomial.X i) ⊓
          Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i))).op
        (Proj.twistPowSection 1 (X_mem_one (R := R) (N := N) i)) =
      (Proj.twist 𝒜 1).presheaf.map
        (homOfLE (inf_le_right : Proj.basicOpen 𝒜 (MvPolynomial.X i) ⊓
          Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ Proj.basicOpen 𝒜 (MvPolynomial.X j))).op
        (Proj.twistPowSection 1 (X_mem_one (R := R) (N := N) j)) := by
  refine Subtype.ext (funext fun point ↦ Subtype.ext ?_)
  have hpi : point.1 ∈ Proj.basicOpen 𝒜 (MvPolynomial.X i) :=
    (inf_le_left : Proj.basicOpen 𝒜 (MvPolynomial.X i) ⊓ Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ _) point.2
  have hpj : point.1 ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j) :=
    (inf_le_right : Proj.basicOpen 𝒜 (MvPolynomial.X i) ⊓ Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ _) point.2
  have h3 := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 (MvPolynomial.X i)
    (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio R N i j) ⟨point.1, hpi⟩
  haveI : point.1.asHomogeneousIdeal.toIdeal.IsPrime := point.1.isPrime
  change ((Proj.awayToSection 𝒜 (MvPolynomial.X i)
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio R N i j)).1 ⟨point.1, hpi⟩).val *
      ((Proj.twistPowSection 1 (X_mem_one (R := R) (N := N) i)).1 ⟨point.1, hpi⟩ :
        Localization.AtPrime point.1.asHomogeneousIdeal.toIdeal) =
    ((Proj.twistPowSection 1 (X_mem_one (R := R) (N := N) j)).1 ⟨point.1, hpj⟩ :
        Localization.AtPrime point.1.asHomogeneousIdeal.toIdeal)
  have e1 := Proj.val_twistPowSection_apply 1 (X_mem_one (R := R) (N := N) i) ⟨point.1, hpi⟩
  have e2 := Proj.val_twistPowSection_apply 1 (X_mem_one (R := R) (N := N) j) ⟨point.1, hpj⟩
  refine (congrArg₂ (· * ·) h3 e1).trans (Eq.trans ?_ e2.symm)
  simp only [ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    RingHom.id_apply]
  rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq]
  simp [mul_comm]

/-- Degree `n`: `(X_j / X_i)ⁿ • X_iⁿ = X_jⁿ` on the overlap (W07's multiplicative transition rule). -/
theorem twistPow_rel (i j : Fin (N + 1)) : ∀ n : ℕ,
    ratioOn (R := R) i j ^ n • (Proj.twist 𝒜 n).presheaf.map
        (homOfLE (inf_le_left : Proj.basicOpen 𝒜 (MvPolynomial.X i) ⊓
          Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i))).op
        (Proj.twistPowSection n (X_mem_one (R := R) (N := N) i)) =
      (Proj.twist 𝒜 n).presheaf.map
        (homOfLE (inf_le_right : Proj.basicOpen 𝒜 (MvPolynomial.X i) ⊓
          Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ Proj.basicOpen 𝒜 (MvPolynomial.X j))).op
        (Proj.twistPowSection n (X_mem_one (R := R) (N := N) j))
  | 0 => by
    rw [pow_zero, one_smul]
    exact twistPow_zero_rel i j
  | n + 1 => by
    have := Proj.twistPowSection_map_eq_mul_smul (X_mem_one (R := R) (N := N) j)
      (X_mem_one (R := R) (N := N) i) inf_le_right inf_le_left (twistPow_rel i j n)
      (twistPow_one_rel i j)
    rw [← pow_succ] at this
    exact this

/-- Composite restriction of functions. -/
theorem presheaf_map_map {X : Scheme.{u}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(X, U)) :
    X.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE h1).op a) =
      X.presheaf.map (homOfLE (h2.trans h1)).op a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules}
  (𝔓 : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation M f N)

/-- The pulled-back twist `𝔓.toProj^* 𝒪(n)`. -/
abbrev pulledTwistPow (n : ℕ) : X.Modules :=
  (Scheme.Modules.pullback 𝔓.toProj).obj (Proj.twist 𝒜 (n : ℤ))

/-- The pulled-back power section `X_iⁿ` on the chart of `X_i`. -/
def pulledPow (i : Fin (N + 1)) (n : ℕ) : Γ(pulledTwistPow 𝔓 n, chart 𝔓 i) :=
  pullbackSection 𝔓.toProj (Proj.twistPowSection (n : ℤ) (X_mem_one (R := R) (N := N) i))

theorem isFreeGenerator_pulledPow (i : Fin (N + 1)) (n : ℕ) : IsFreeGenerator (pulledPow 𝔓 i n) :=
  (Proj.isFreeGenerator_twistPowSection (n : ℤ) (X_mem_one (R := R) (N := N) i)).pullbackSection
    𝔓.toProj

/-- The given section's chart restriction is a Source frame on its chart. -/
theorem isFrameOn_chartSigma (i : Fin (N + 1)) :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsFrameOn
      (chartSigma 𝔓 i) (chart 𝔓 i) := by
  intro W hWU _
  rw [chartSigma, presheaf_map_homOfLE_map_homOfLE]
  exact 𝔓.frame i W hWU

/-- The Source tensor-power section of the chart frame. -/
abbrev chartSigmaPow (i : Fin (N + 1)) (n : ℕ) :
    Γ(ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M n, chart 𝔓 i) :=
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPowSection (chartSigma 𝔓 i) n

/-- The pulled-back chart ratio `r_ij = 𝔓.toProj^*(X_j / X_i)` on the chart of `X_i`. -/
abbrev chartRatio (i j : Fin (N + 1)) : Γ(X, chart 𝔓 i) :=
  𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X i))
    (Proj.awayToSection 𝒜 (MvPolynomial.X i)
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio R N i j))

/-- Twist side: on `W ⊆` both charts, `X_jⁿ = (r_ij|_W)ⁿ • X_iⁿ`. -/
theorem pulledPow_rel (i j : Fin (N + 1)) (n : ℕ) {W : X.Opens} (hi : W ≤ chart 𝔓 i)
    (hj : W ≤ chart 𝔓 j) :
    (pulledTwistPow 𝔓 n).presheaf.map (homOfLE hj).op (pulledPow 𝔓 j n) =
      (X.presheaf.map (homOfLE hi).op (chartRatio 𝔓 i j)) ^ n •
        (pulledTwistPow 𝔓 n).presheaf.map (homOfLE hi).op (pulledPow 𝔓 i n) := by
  have hV : W ≤ 𝔓.toProj ⁻¹ᵁ (Proj.basicOpen 𝒜 (MvPolynomial.X i) ⊓
      Proj.basicOpen 𝒜 (MvPolynomial.X j)) := le_inf hi hj
  -- pull the W07 relation back and restrict it to `W`
  have rel := congrArg (pullbackSection 𝔓.toProj) (twistPow_rel (R := R) (N := N) i j n)
  rw [pullbackSection_smul, pullbackSection_map, pullbackSection_map] at rel
  have rel' := congrArg ((pulledTwistPow 𝔓 n).presheaf.map (homOfLE hV).op) rel
  rw [map_smul, presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE] at rel'
  rw [pulledPow, pulledPow, ← rel']
  congr 1
  rw [map_pow, map_pow, ratioOn, app_map_apply, presheaf_map_map]

/-- Given side: on `W ⊆` both charts, `σ_jⁿ = (r_ij|_W)ⁿ • σ_iⁿ` for the literal Source tensor power. -/
theorem chartSigmaPow_rel (i j : Fin (N + 1)) (n : ℕ) {W : X.Opens} (hi : W ≤ chart 𝔓 i)
    (hj : W ≤ chart 𝔓 j) :
    (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M n).presheaf.map
        (homOfLE hj).op (chartSigmaPow 𝔓 j n) =
      (X.presheaf.map (homOfLE hi).op (chartRatio 𝔓 i j)) ^ n •
        (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M n).presheaf.map
          (homOfLE hi).op (chartSigmaPow 𝔓 i n) := by
  have hσ : M.presheaf.map (homOfLE hj).op (chartSigma 𝔓 j) =
      X.presheaf.map (homOfLE hi).op (chartRatio 𝔓 i j) • M.presheaf.map (homOfLE hi).op (chartSigma 𝔓 i) := by
    rw [chartSigma, presheaf_map_homOfLE_map_homOfLE, ← map_smul, chartSigma, chartRatio,
      𝔓.app_ratio_smul i j, presheaf_map_homOfLE_map_homOfLE]
  rw [chartSigmaPow, chartSigmaPow,
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.map_tensorPowSection,
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.map_tensorPowSection, hσ,
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPowSection_smul]

/-- The pairs `(X_iⁿ|_W, σ_iⁿ|_W)`. -/
def framePairsPow (n : ℕ) (W : X.Opens) :
    Set (Γ(pulledTwistPow 𝔓 n, W) ×
      Γ(ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M n, W)) :=
  {pq | ∃ (i : Fin (N + 1)) (h : W ≤ chart 𝔓 i),
    pq = ((pulledTwistPow 𝔓 n).presheaf.map (homOfLE h).op (pulledPow 𝔓 i n),
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M n).presheaf.map
        (homOfLE h).op (chartSigmaPow 𝔓 i n))}

/-- **Corner B.** For every `n` (including `0`), the pulled-back `𝒪(n)` is isomorphic to the LITERAL
Source tensor power `M.tensorPow n`, sending the pulled-back `X_iⁿ` to `tensorPowSection σ_i n` on the
chart of `X_i`. -/
theorem exists_iso_pullback_twist_tensorPow (n : ℕ) :
    ∃ e : pulledTwistPow 𝔓 n ≅
        ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M n,
      ∀ i : Fin (N + 1), e.hom.app (chart 𝔓 i) (pulledPow 𝔓 i n) = chartSigmaPow 𝔓 i n := by
  obtain ⟨e, he⟩ : ∃ e : pulledTwistPow 𝔓 n ≅
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M n,
      ∀ (W : X.Opens) (pq : Γ(pulledTwistPow 𝔓 n, W) ×
        Γ(ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M n, W)),
        pq ∈ framePairsPow 𝔓 n W → e.hom.app W pq.1 = pq.2 := by
    refine ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul
      (framePairsPow 𝔓 n) ?_ ?_ ?_ ?_
    · rintro W pq ⟨i, h, rfl⟩
      constructor
      · intro W' hWU _
        rw [presheaf_map_homOfLE_map_homOfLE]
        exact isFreeGenerator_pulledPow 𝔓 i n W' (hWU.trans h)
      · exact (((isFrameOn_chartSigma 𝔓 i).tensorPowSection n).map (homOfLE h)).mono h
    · intro x
      obtain ⟨i, hi⟩ := chart_cover 𝔓 x
      exact ⟨chart 𝔓 i, hi, ⟨_, i, le_rfl, rfl⟩⟩
    · rintro W W' hW' pq ⟨i, h, rfl⟩
      refine ⟨i, hW'.trans h, ?_⟩
      simp only [presheaf_map_homOfLE_map_homOfLE]
    · rintro W pq pq' ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
      exact ⟨(X.presheaf.map (homOfLE hi).op (chartRatio 𝔓 i j)) ^ n,
        pulledPow_rel 𝔓 i j n hi hj, chartSigmaPow_rel 𝔓 i j n hi hj⟩
  refine ⟨e, fun i => ?_⟩
  have := he (chart 𝔓 i) _ ⟨i, le_rfl, rfl⟩
  simpa using this


/-- **Corner B at `n = 0`**, spelled out: the pulled-back `𝒪(0)` is isomorphic to the Source unit
`M.tensorPow 0 = 𝟙_`, sending the pulled-back `X_i⁰` to the Source `unitSection` on each chart. -/
theorem exists_iso_pullback_twist_tensorPow_zero :
    ∃ e : pulledTwistPow 𝔓 0 ≅
        ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M 0,
      ∀ i : Fin (N + 1), e.hom.app (chart 𝔓 i) (pulledPow 𝔓 i 0) =
        ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.unitSection (chart 𝔓 i) :=
  exists_iso_pullback_twist_tensorPow 𝔓 0


end CornerB

end ZInQ.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower
