import ZInQKernel.Contrib.CurvesG.GenusSplit
import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.CanonicalDegree
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.Dim.Basic

/-! # modular-split, row dimJacobianEqGenus: `ZInQ.Contrib.CurvesG.DimJacobianEqGenus` without literature leaves

The row (bundle field `dimJacobianEqGenus`, `ZInQKernel/Contrib/CurvesG/GenusSplit.lean`) is imported, not
copied. Its sources were Milne, *Jacobian varieties*, Prop. 2.1 (`T₀J ≅ H¹(X, 𝒪_X)`) with Serre duality
(`dim H¹(X, 𝒪_X) = dim H⁰(X, Ω¹)`) and the identification of `H⁰(X, Ω¹)` with the differentials of the
function field regular at every place. The first two are now **Lean proofs** in the kernel, through the
vendored Jacobian-Challenge library (`ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/`, Apache-2.0):
* `AlgebraicGeometry.exists_abelianVariety_picardDegreeZero`: `Pic⁰` of the curve is represented by an
  abelian variety, **smooth of relative dimension `arithmeticGenus = dim H¹(X, 𝒪_X)`**;
* `AlgebraicGeometry.Curve.isAlbanese_abelJacobiMap`: it is the Albanese variety (so it is `J` up to
  isomorphism, `LeafModCurves.IsJacobian.unique`);
* `AlgebraicGeometry.Scheme.Modules.finrankH_relativeDifferentials_zero_eq_genus`: **Serre duality**,
  `dim H⁰(X, Ω¹_{X/ℚ}) = arithmeticGenus`;
* `ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension` (kernel): `dim = n` for smooth of
  relative dimension `n`.
What is left is one GLUE statement over genuine definitions, `H0DifferentialsEqHolo` (no literature leaf). -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

namespace ModularSplit.DimJac

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves ZInQ.Contrib.CurvesG

/-- **GLUE (named, unproved): `H⁰(X, Ω¹_{X/ℚ})` is the space of differentials of the function field
regular at every place.** For a smooth proper geometrically connected integral curve `X/ℚ` and a field `F`
isomorphic to its function field, `dim_ℚ H⁰(X, Ω¹_{X/ℚ}) = g(F)` (`CurvesG.fieldGenus`, Chevalley's
definition). Needs: `H⁰(X, M) = Γ(X, M)` for the library's sheaf cohomology; `Γ(X, Ω¹) = ⋂_x Ω_{𝒪_{X,x}/ℚ}`
inside `Ω_{F/ℚ}` (`Ω¹` locally free of rank one, `X` integral; on affine opens `Γ(U, Ω¹) = Ω_{Γ(U)/ℚ}` is the
library's `Scheme.Hom.kaehlerSectionsEquiv`, then localization); the image of `Ω_{𝒪_{X,x}/ℚ}` in `Ω_{F/ℚ}` is
`CurvesG.regularAt F 𝒪_{X,x}`; every valuation subring of `F` containing `ℚ` other than `F` is a local ring
`𝒪_{X,x}` at a closed point (`X` proper: valuative criterion; `X` normal of dimension one: `𝒪_{X,x}` is a
DVR), and conversely. Standard (Hartshorne II.8, II.6.7, II.4.7; Stichtenoth 1.5; UNVERIFIED numbers);
project glue, no published-theorem content beyond textbook sheaf theory. -/
def H0DifferentialsEqHolo : Prop :=
  ∀ (X : Over SpecQ) (_ : IsCurve X) (_ : IsIntegral X.left) (F : Type) [Field F] [Algebra ℚ F],
    Nonempty (X.left.functionField ≃+* F) →
    letI : X.left.Over SpecQ := ⟨X.hom⟩
    (X.left ↘ SpecQ).relativeDifferentials.finrankH ℚ 0 = fieldGenus F

/-- **Lean, from the vendored library: a Jacobian has dimension `arithmeticGenus = dim H¹(X, 𝒪_X)`.** -/
theorem dim_jacobian_eq_arithmeticGenus (X : Over SpecQ) (hX : IsCurve X) (P₀ : RatPt X)
    (J : PkgI3.AbVar ℚ) (aj : X ⟶ J.X) (hJ : IsJacobian X P₀ J aj) :
    letI : X.left.Over SpecQ := ⟨X.hom⟩
    J.dim = ((X.left.arithmeticGenus ℚ : ℕ) : WithBot ℕ∞) := by
  letI : X.left.Over SpecQ := ⟨X.hom⟩
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  have : GeometricallyIrreducible X.hom := inferInstance
  have : SmoothOfRelativeDimension 1 (X.left ↘ SpecQ) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  have : IsProper (X.left ↘ SpecQ) := inferInstanceAs (IsProper X.hom)
  have : GeometricallyIntegral (X.left ↘ SpecQ) :=
    inferInstanceAs (GeometricallyIntegral X.hom)
  obtain ⟨variety, representation, tensorCompatible, hsm⟩ :=
    exists_abelianVariety_picardDegreeZero (baseField := ℚ) X.left
  let aj' : X ⟶ variety.group.X :=
    Curve.abelJacobiMap ⟨X⟩ P₀.left (by simp) representation
  have alb : IsAlbanese P₀ variety aj' :=
    Curve.isAlbanese_abelJacobiMap ⟨X⟩ P₀ variety representation tensorCompatible
  have : GeometricallyIntegral variety.group.X.hom :=
    Smooth.geometricallyIntegral variety.group.X.hom
  let J' : PkgI3.AbVar ℚ :=
    { X := variety.group.X
      grp := variety.group.grp
      proper := variety.proper
      smooth := variety.smooth
      geomInt := inferInstance }
  have hJ' : IsJacobian X P₀ J' aj' := by
    refine ⟨alb.1, ?_⟩
    intro A f hf
    obtain ⟨g, hg, huniq⟩ := alb.existsUnique_schemeMap f hf
    have pointed : η[variety.group.X] ≫ g = η[A.X] := by
      rw [← alb.1, Category.assoc, ← hg, hf]
    have : IsMonHom g := isMonHom_of_isProper_of_geometricallyIntegral g pointed
    exact ⟨g, ⟨inferInstance, hg.symm⟩, fun φ hφ => huniq φ hφ.2.symm⟩
  obtain ⟨e, -, -, -⟩ := IsJacobian.unique hJ hJ'
  have hiso : J.X.left ≅ variety.group.X.left := (Over.forget _).mapIso e
  have hne : Nonempty variety.group.X.left := by
    have : Nonempty (Spec (CommRingCat.of ℚ)) := inferInstance
    obtain ⟨x⟩ := this
    exact ⟨(η[variety.group.X] : 𝟙_ (Over SpecQ) ⟶ variety.group.X).left.base x⟩
  change topologicalKrullDim J.X.left = _
  rw [ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_iso hiso,
    ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension variety.group.X.hom
      (X.left.arithmeticGenus ℚ)]

/-- **Row dimJacobianEqGenus from the one glue statement `H0DifferentialsEqHolo`.** -/
theorem dimJacobianEqGenus_of_glue (hG : H0DifferentialsEqHolo) : DimJacobianEqGenus := by
  intro X hX P₀ J aj hJ hI F _ _ he
  letI : X.left.Over SpecQ := ⟨X.hom⟩
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  have : GeometricallyIrreducible (X.left ↘ SpecQ) :=
    inferInstanceAs (GeometricallyIrreducible X.hom)
  have : SmoothOfRelativeDimension 1 (X.left ↘ SpecQ) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  have : IsProper (X.left ↘ SpecQ) := inferInstanceAs (IsProper X.hom)
  rw [dim_jacobian_eq_arithmeticGenus X hX P₀ J aj hJ,
    ← Scheme.Modules.finrankH_relativeDifferentials_zero_eq_genus (baseField := ℚ) (source := X.left),
    hG X hX hI F he]

end ModularSplit.DimJac

#print axioms ModularSplit.DimJac.dimJacobianEqGenus_of_glue
