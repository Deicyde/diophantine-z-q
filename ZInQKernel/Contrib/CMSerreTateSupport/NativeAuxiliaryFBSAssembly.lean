/-
Copyright (c) 2026 H5 contributors. Apache-2.0.

# An auxiliary native finite-by-sections line

Choose an affine neighbourhood of the original group identity. The native
Cartier complement supplies its dual line and canonical nonzero section.
Its divisor stabilizer is finite, and the actual square presentation gives
a finite-by-sections tensor square on the same abelian variety.

This line is auxiliary. It does not replace the original line used for
field descent. All fields, group laws, sections, ideals and native tensor
powers remain those given by the constructions below.
-/
import ZInQKernel.Contrib.CMSerreTateSupport.NativeAffineCartierLine
import ZInQKernel.Contrib.CMSerreTateSupport.NativeAffineComplementStabilizer
import ZInQKernel.Contrib.CMSerreTateSupport.NativeApplicationOneAssembly

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.NativeAuxiliaryFBSAssembly

/-- EXACT C3 I0 interface, from its true native producer sub-goals. The
auxiliary line is an ACTUAL native positive power on the SAME original A.
No arbitrary supplied FBS/ample line or model is assumed. -/
theorem existsFBSLine
    (hAffineCore : H5OriginalDVR.Lane2.Step2DelegatedInterfaces.SameAbVarAffineComplement.{u})
    (hFiniteSquare : H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSquarePresentation.{u}) :
    ZInQ.Contrib.CloudR2NOS.Step1.ExistsFBSLine.{u} := by
  intro K _ _ A _
  let e : A.X.left := (η[A.X]).left (IsLocalRing.closedPoint K)
  obtain ⟨U, hU, hunit, _⟩ :=
    exists_isAffineOpen_mem_and_subset (x := e) (U := ⊤) trivial
  obtain ⟨N, hN, hData⟩ :=
    H5OriginalDVR.Lane2.NativeAffineCartierLine.auxiliary_effective_line_of_affine_complement
      hAffineCore A U hU hunit
  letI := hN
  obtain ⟨θ, hθ, D, hD, hsupp, hZero, hND⟩ := hData
  have hUnit : (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) = η[A.X] :=
    (CategoryTheory.MonObj.one_eq_one A.X).symm
  have hUnitPoint : H5OriginalDVR.Lane2.NativeAffineComplementStabilizer.pt A 1 ∈ U := by
    rw [hUnit]
    exact hunit
  have hHD : (H5OriginalDVR.Lane2.NativeDivisorKernel.divisorStabilizer A D).Finite :=
    H5OriginalDVR.Lane2.NativeAffineComplementStabilizer.divisorStabilizer_finite_of_affine_complement
      A D U hU hUnitPoint hsupp
  have hFBS :
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
        (R := K) (Scheme.Modules.tensorPow N 2) A.X.hom :=
    H5OriginalDVR.Lane2.NativeApplicationOneAssembly.native_square_finite_by_sections
      hFiniteSquare A N θ hθ D hD hZero hND hHD
  exact ⟨Scheme.Modules.tensorPow N 2, inferInstance, hFBS⟩

end H5OriginalDVR.Lane2.NativeAuxiliaryFBSAssembly
