/-
H5 Step2 / I0: native auxiliary finite-by-sections assembly on SAME Hbar.
Copyright (c) 2026 H5 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. The actual C5/C3 producer proofs and C6 truth/
Source review remain required; no Native/kernel/Std3/ABI acceptance.

Inputs are EXACT pending producer theorems from the ONE frozen4d5 file:
C5 SameAbVarAffineComplement and C3 FiniteSquarePresentation. Neither is an
assumed Factory, ample/FBS/model/line/nondegeneracy Fact or original NOS input.
All eight delegated Props have C6's mathematical TRUE verdict (ledger v003,
b27e1777), not their native Source proofs or kernel acceptance.

The proof chooses an ACTUAL affine neighbourhood of the ORIGINAL group unit
on SAME A. C5 constructs native Cartier D_U with complement support. Lane2
constructs actual N=D_U.toModules-dual/theta, complete zero IDEAL D_U and
theta≠0. Its OWN native affine/complete-coset argument proves H(D_U) finite,
reusing C3's genuine generic E3 Source d292 as a single producer. The actual
native square/pair sections/frames/G5 make an N^2 presentation; C3 proves
THAT map finite. Choose AUXILIARY native N^2 as I0's SOME FBS line on SAME A.

No Euler/RR/χ premise, no original-k descent, no replacement of descent Ms,
M or beta by this auxiliary line. Every characteristic and dimension, u.
Received GM9 bodies are attributed BLUEPRINTS ONLY; no Stacks import/bridge,
new intake, Native/parser/helper/AST, source-budget/root/protected edit.
-/
import NativeAffineCartierLine
import NativeAffineComplementStabilizer
import NativeApplicationOneAssembly

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
  let e := (η[A.X]).left (IsLocalRing.closedPoint K)
  obtain ⟨U, hU, hunit, _⟩ :=
    exists_isAffineOpen_mem_and_subset (x := e) (U := ⊤) trivial
  obtain ⟨N, hN, θ, hθ, D, hD, hsupp, hZero, hND⟩ :=
    H5OriginalDVR.Lane2.NativeAffineCartierLine.auxiliary_effective_line_of_affine_complement
      hAffineCore A U hU hunit
  letI := hN
  have hUnitPoint : H5OriginalDVR.Lane2.NativeAffineComplementStabilizer.pt A 1 ∈ U := by
    simpa [H5OriginalDVR.Lane2.NativeAffineComplementStabilizer.pt,
      MonObj.Hom.one_def, Over.comp_left, Over.toUnit_left, e] using hunit
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
