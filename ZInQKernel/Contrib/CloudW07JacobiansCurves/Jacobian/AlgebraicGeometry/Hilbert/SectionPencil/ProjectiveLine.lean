-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.ProjectiveLine), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.Core
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.Divisor
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist

/-!
# The projective-line pencil of two sections

The coefficients are the two actual coordinate sections of the relative
projective line. The ideal below is the zero locus of their tensor sum, rather
than a family specified through a class in a Picard group.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SectionPencil

variable {source base : Scheme.{u}}

/-- The line bundle of the pencil on the product with the relative projective line. -/
abbrev projectiveLineBundle (structureMap : source ⟶ base) (lineBundle : source.Modules) :
    (Limits.pullback structureMap (ℙ(ULift.{u} (Fin 2); base) ↘ base)).Modules :=
  pencilLine (Limits.pullback.fst structureMap (ℙ(ULift.{u} (Fin 2); base) ↘ base))
    (Limits.pullback.snd structureMap (ℙ(ULift.{u} (Fin 2); base) ↘ base))
    lineBundle (ProjectiveSpace.twist (ULift.{u} (Fin 2)) base 1)

/-- The section whose coefficients are the two homogeneous coordinates. -/
def projectiveLineSection (structureMap : source ⟶ base) {lineBundle : source.Modules}
    (firstSection secondSection : unit source ⟶ lineBundle) :
    unit (Limits.pullback structureMap (ℙ(ULift.{u} (Fin 2); base) ↘ base)) ⟶
      projectiveLineBundle structureMap lineBundle :=
  pencilSection (Limits.pullback.fst structureMap (ℙ(ULift.{u} (Fin 2); base) ↘ base))
    (Limits.pullback.snd structureMap (ℙ(ULift.{u} (Fin 2); base) ↘ base))
    firstSection secondSection
    (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) base ⟨0⟩ 1)
    (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) base ⟨1⟩ 1)

/-- The actual ideal of the projective-line pencil. -/
def projectiveLineIdeal (structureMap : source ⟶ base) {lineBundle : source.Modules}
    [lineBundle.IsInvertible] (firstSection secondSection : unit source ⟶ lineBundle) :
    (Limits.pullback structureMap (ℙ(ULift.{u} (Fin 2); base) ↘ base)).IdealSheafData :=
  (projectiveLineSection structureMap firstSection secondSection).zeroLocus

/-- Pulling back the pencil ideal gives the zero scheme of the actual pulled section. -/
theorem projectiveLineIdeal_comap (structureMap : source ⟶ base)
    {lineBundle : source.Modules} [lineBundle.IsInvertible]
    (firstSection secondSection : unit source ⟶ lineBundle) {test : Scheme.{u}}
    (restriction : test ⟶ Limits.pullback structureMap (ℙ(ULift.{u} (Fin 2); base) ↘ base)) :
    (projectiveLineIdeal structureMap firstSection secondSection).comap restriction =
      (pullbackSectionHom restriction
        (projectiveLineSection structureMap firstSection secondSection)).zeroLocus :=
  (pullbackSectionHom_zeroLocus restriction _).symm

end AlgebraicGeometry.SectionPencil
