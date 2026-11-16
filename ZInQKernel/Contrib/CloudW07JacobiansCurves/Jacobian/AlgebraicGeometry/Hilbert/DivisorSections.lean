-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Hilbert.DivisorSections), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.Sections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.AbelMap

/-!
# Sections of linearly equivalent Hilbert divisors

Two relative Hilbert divisors with the same Picard class are the zero schemes
of two nonzero sections of the same actual dual-ideal line bundle.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

/-- Equal divisor classes give two actual nonzero sections on the first divisor
line, with their original zero ideals and nonzero zeroth cohomology classes. -/
theorem exists_nonzero_sections_of_abelClass_eq
    {sourceScheme baseScheme : Scheme.{u}} (structureMap : sourceScheme ⟶ baseScheme)
    [SmoothOfRelativeDimension 1 structureMap] {degree : ℕ} {parameter : Over baseScheme}
    [Nonempty (pullback (C := Scheme.{u}) structureMap parameter.hom)]
    (first second : (hilbertPresheaf structureMap degree).obj (op parameter))
    (class_eq : abelClass structureMap first = abelClass structureMap second) :
    letI := first.2.isInvertible.isInvertible_dual_toModules
    ∃ firstSection secondSection : Modules.unit (pullback structureMap parameter.hom) ⟶
        first.1.toModulesᵛ,
      firstSection.zeroLocus = first.1 ∧ secondSection.zeroLocus = second.1 ∧
        firstSection ≠ 0 ∧ secondSection ≠ 0 ∧
          Modules.H.unitHomAddEquiv first.1.toModulesᵛ firstSection ≠ 0 ∧
            Modules.H.unitHomAddEquiv first.1.toModulesᵛ secondSection ≠ 0 := by
  letI := first.2.isInvertible.isInvertible_toModules
  letI := second.2.isInvertible.isInvertible_toModules
  obtain ⟨comparison⟩ := Pic.eq_iff_nonempty_iso.mp class_eq
  let idealComparison := (abelClassIso structureMap first).symm ≪≫ comparison ≪≫
    abelClassIso structureMap second
  obtain ⟨firstSection, first_zeroLocus, first_nonzero, first_cohomology⟩ :=
    first.2.isInvertible.exists_nonzero_section_of_iso first.1.toModulesᵛ (Iso.refl _)
  obtain ⟨secondSection, second_zeroLocus, second_nonzero, second_cohomology⟩ :=
    second.2.isInvertible.exists_nonzero_section_of_iso first.1.toModulesᵛ idealComparison.symm
  exact ⟨firstSection, secondSection, first_zeroLocus, second_zeroLocus,
    first_nonzero, second_nonzero, first_cohomology, second_cohomology⟩

end AlgebraicGeometry
