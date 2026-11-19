/-
# H5 / NOS round 2, lane 1: a finite ProjPresentation's line is the pulled-back 𝒪(1) — and its powers

Newly authored glue (H5 round-2 lane 1, 2026-11-15). Inputs, all read-only and unchanged:
* the canonical Source port (lane 4) of the FLT development (anthropics/fermats-last-theorem @
  6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, Copyright 2026 Anthropic, PBC): the LITERAL
  `Scheme.Modules.ProjPresentation` structure (sections `σ`, map `toProj` to Mathlib's
  `Proj (homogeneousSubmodule (Fin (N+1)) R)`, frames, coordinate-ratio equations) and its iso criterion
  `Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul`;
* the vendored W07 contribution (frenzymath/Jacobian-Challenge @ c4254cce15b3e284a0a3ae1d73936f2ee195d272,
  Apache-2.0, Copyright 2026 Axel Delaval, Jie Xu and Shitan Xu): Serre twisting sheaves `Proj.twist`,
  the coordinate sections `Proj.unitToTwist`, their free-generator property and transition rule, and
  free generators under pullback.

Corner A (`exists_iso_pullback_twist_one`): for the ACTUAL presentation `𝔓 : M.ProjPresentation f N`
(any commutative ring `R`, any universe), the given module `M` is isomorphic to `𝔓.toProj^* 𝒪(1)` by an
isomorphism sending the pulled-back coordinate section `X_i` to `σ_i` on every chart `𝔓.toProj⁻¹ D₊(X_i)`.
It is constructed from the presentation's own frames and ratio equations; no isomorphism, ampleness,
finiteness or closed-immersion input is used.
-/
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Pullback
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Local

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower

section CornerA

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {M : X.Modules} {N : ℕ}

/-- The grading of the polynomial ring in `N + 1` variables. -/
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

/-- `X_i` has degree one. -/
theorem X_mem_one (i : Fin (N + 1)) : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R) ∈ 𝒜 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R i)

theorem X_mem_one' (i : Fin (N + 1)) :
    (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R) ∈ 𝒜 (1 • 1) := by
  simpa using X_mem_one (R := R) (N := N) i

/-- W07's global coordinate section `X_i` of `𝒪(1)` on `Proj`. -/
def coordSection (i : Fin (N + 1)) : Γ(Proj.twist 𝒜 (0 + ((1 : ℕ) : ℤ)), ⊤) :=
  (Proj.unitToTwist (X_mem_one (R := R) (N := N) i)).app ⊤ (1 : Γ(Proj 𝒜, ⊤))

theorem coordSection_map (i : Fin (N + 1)) {V : (Proj 𝒜).Opens} (h : V ≤ ⊤) :
    (Proj.twist 𝒜 (0 + ((1 : ℕ) : ℤ))).presheaf.map (homOfLE h).op (coordSection i) =
      (Proj.unitToTwist (X_mem_one (R := R) (N := N) i)).app V (1 : Γ(Proj 𝒜, V)) := by
  have h1 := Hom.app_presheaf_map (Proj.unitToTwist (X_mem_one (R := R) (N := N) i)) (homOfLE h)
    (1 : Γ(Proj 𝒜, ⊤))
  refine h1.symm.trans ?_
  congr 1

/-- W07: on `D₊(X_i)`, `X_i` is a free generator of `𝒪(1)`. -/
theorem isFreeGenerator_coordSection (i : Fin (N + 1)) :
    IsFreeGenerator ((Proj.twist 𝒜 (0 + ((1 : ℕ) : ℤ))).presheaf.map
      (homOfLE (le_top : Proj.basicOpen 𝒜 (MvPolynomial.X i) ≤ ⊤)).op (coordSection i)) := by
  rw [coordSection_map]
  exact Proj.isFreeGenerator_unitToTwist (X_mem_one (R := R) (N := N) i)

/-- W07 transition rule on `D₊(X_i)`: `X_j = (X_j / X_i) • X_i`, with the SAME ratio element as the
Source's `ProjSpace.ratio`. -/
theorem coordSection_map_eq_smul (i j : Fin (N + 1)) :
    (Proj.twist 𝒜 (0 + ((1 : ℕ) : ℤ))).presheaf.map
        (homOfLE (le_top : Proj.basicOpen 𝒜 (MvPolynomial.X i) ≤ ⊤)).op (coordSection j) =
      Proj.awayToSection 𝒜 (MvPolynomial.X i)
          (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio R N i j) •
        (Proj.twist 𝒜 (0 + ((1 : ℕ) : ℤ))).presheaf.map
          (homOfLE (le_top : Proj.basicOpen 𝒜 (MvPolynomial.X i) ≤ ⊤)).op (coordSection i) :=
  Proj.map_unitToTwist_eq_smul (X_mem_one (R := R) (N := N) j) (X_mem_one (R := R) (N := N) i)
    (X_mem_one' (R := R) (N := N) j)

variable (𝔓 : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation M f N)

/-- The chart `𝔓.toProj⁻¹ D₊(X_i)`. -/
abbrev chart (i : Fin (N + 1)) : X.Opens := 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i)

/-- The pulled-back twist `𝔓.toProj^* 𝒪(1)`. -/
abbrev pulledTwist : X.Modules :=
  (Scheme.Modules.pullback 𝔓.toProj).obj (Proj.twist 𝒜 (0 + ((1 : ℕ) : ℤ)))

/-- The pulled-back coordinate section `X_i`, restricted to its chart. -/
def pulledCoord (i : Fin (N + 1)) : Γ(pulledTwist 𝔓, chart 𝔓 i) :=
  (pulledTwist 𝔓).presheaf.map (homOfLE (𝔓.toProj.preimage_mono le_top)).op
    (pullbackSection 𝔓.toProj (coordSection (R := R) (N := N) i))

theorem pulledCoord_eq (i : Fin (N + 1)) :
    pulledCoord 𝔓 i = pullbackSection 𝔓.toProj ((Proj.twist 𝒜 (0 + ((1 : ℕ) : ℤ))).presheaf.map
      (homOfLE (le_top : Proj.basicOpen 𝒜 (MvPolynomial.X i) ≤ ⊤)).op (coordSection i)) :=
  (pullbackSection_map 𝔓.toProj le_top _).symm

theorem isFreeGenerator_pulledCoord (i : Fin (N + 1)) : IsFreeGenerator (pulledCoord 𝔓 i) := by
  rw [pulledCoord_eq]
  exact (isFreeGenerator_coordSection i).pullbackSection 𝔓.toProj

/-- The pulled-back transition rule on the chart of `X_i`. -/
theorem pulled_map_eq_smul (i j : Fin (N + 1)) :
    (pulledTwist 𝔓).presheaf.map (homOfLE (𝔓.toProj.preimage_mono le_top)).op
        (pullbackSection 𝔓.toProj (coordSection (R := R) (N := N) j)) =
      𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X i))
          (Proj.awayToSection 𝒜 (MvPolynomial.X i)
            (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio R N i j)) •
        pulledCoord 𝔓 i := by
  rw [← pullbackSection_map 𝔓.toProj (le_top : Proj.basicOpen 𝒜 (MvPolynomial.X i) ≤ ⊤),
    coordSection_map_eq_smul, pullbackSection_smul, ← pulledCoord_eq]

/-- The given section `σ_i`, restricted to its chart. -/
def chartSigma (i : Fin (N + 1)) : Γ(M, chart 𝔓 i) :=
  M.presheaf.map (homOfLE (le_top : chart 𝔓 i ≤ ⊤)).op (𝔓.σ i)

/-- The pairs `(X_i|_W, σ_i|_W)` for `W` inside the chart of `X_i`. -/
def framePairs (W : X.Opens) : Set (Γ(pulledTwist 𝔓, W) × Γ(M, W)) :=
  {pq | ∃ (i : Fin (N + 1)) (h : W ≤ chart 𝔓 i),
    pq = ((pulledTwist 𝔓).presheaf.map (homOfLE h).op (pulledCoord 𝔓 i),
      M.presheaf.map (homOfLE h).op (chartSigma 𝔓 i))}

theorem chart_cover (x : X) : ∃ i : Fin (N + 1), x ∈ chart 𝔓 i := by
  have hx : 𝔓.toProj x ∈ (⨆ i : Fin (N + 1), Proj.basicOpen 𝒜 (MvPolynomial.X i)) := by
    rw [Proj.iSup_basicOpen_eq_top 𝒜 _
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.irrelevant_le_span_X R N)]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨i, hi⟩

/-- **Corner A.** The given module of an ACTUAL `ProjPresentation` is the pulled-back `𝒪(1)`, by an
isomorphism sending the pulled-back coordinate `X_i` to `σ_i` on the chart of `X_i`. -/
theorem exists_iso_pullback_twist_one :
    ∃ e : pulledTwist 𝔓 ≅ M, ∀ i : Fin (N + 1), e.hom.app (chart 𝔓 i) (pulledCoord 𝔓 i) = chartSigma 𝔓 i := by
  obtain ⟨e, he⟩ : ∃ e : pulledTwist 𝔓 ≅ M, ∀ (W : X.Opens) (pq : Γ(pulledTwist 𝔓, W) × Γ(M, W)),
      pq ∈ framePairs 𝔓 W → e.hom.app W pq.1 = pq.2 := by
    refine ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul
      (framePairs 𝔓) ?_ ?_ ?_ ?_
    · -- frames on both sides
      rintro W pq ⟨i, h, rfl⟩
      constructor
      · intro W' hWU _
        rw [presheaf_map_homOfLE_map_homOfLE]
        exact isFreeGenerator_pulledCoord 𝔓 i W' (hWU.trans h)
      · intro W' hWU _
        rw [presheaf_map_homOfLE_map_homOfLE, chartSigma, presheaf_map_homOfLE_map_homOfLE]
        exact 𝔓.frame i W' (hWU.trans h)
    · -- the charts cover
      intro x
      obtain ⟨i, hi⟩ := chart_cover 𝔓 x
      exact ⟨chart 𝔓 i, hi, ⟨_, i, le_rfl, rfl⟩⟩
    · -- restriction-closed
      rintro W W' hW' pq ⟨i, h, rfl⟩
      refine ⟨i, hW'.trans h, ?_⟩
      simp only [presheaf_map_homOfLE_map_homOfLE]
    · -- the common unit is the pulled-back ratio `X_j / X_i`
      rintro W pq pq' ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
      refine ⟨X.presheaf.map (homOfLE hi).op (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X i))
        (Proj.awayToSection 𝒜 (MvPolynomial.X i)
          (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio R N i j))), ?_, ?_⟩
      · have key := presheaf_map_homOfLE_eq_smul (moduleSheaf := pulledTwist 𝔓)
          (𝔓.toProj.preimage_mono (le_top : Proj.basicOpen 𝒜 (MvPolynomial.X i) ≤ ⊤)) hi
          (exponent := pullbackSection 𝔓.toProj (coordSection (R := R) (N := N) j))
          (otherExponent := pullbackSection 𝔓.toProj (coordSection (R := R) (N := N) i))
          (pulled_map_eq_smul 𝔓 i j)
        simp only [pulledCoord, presheaf_map_homOfLE_map_homOfLE]
        exact key
      · have key := presheaf_map_homOfLE_eq_smul (moduleSheaf := M)
          (le_top : chart 𝔓 i ≤ ⊤) hi (exponent := 𝔓.σ j) (otherExponent := 𝔓.σ i)
          (𝔓.app_ratio_smul i j).symm
        simp only [chartSigma, presheaf_map_homOfLE_map_homOfLE]
        exact key
  refine ⟨e, fun i => ?_⟩
  have := he (chart 𝔓 i) _ ⟨i, le_rfl, rfl⟩
  simpa using this

end CornerA

end ZInQ.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower
