/-
Copyright (c) 2026 H5/NOS Round-2 Lane2 contributors.
Released under the Apache License, Version 2.0.

NEW disjoint SPECIAL FIELD effectivity bridge. Reuses only actual W07
c4254cce15b3e284a0a3ae1d73936f2ee195d272 cohomology/line-zero-locus APIs.
The original W07 LICENSE/NOTICE and source files are unchanged.

Positive ACTUAL H0 of the GIVEN native line gives a nonzero structure-module
morphism, hence a genuine effective Cartier ideal on the SAME integral scheme,
with the actual M ≅ O(D) isomorphism. No chosen section, effective divisor,
finite stabilizer, principal square root or ample conclusion is an input.

SOURCE CANDIDATE ONLY UNTIL THE ONE APPROVED W07 DONOR EPOCH IS FROZEN.
This is not chi -> finite Picard kernel, relative very-ampleness, or NOS.
No alternate/private W07 library or pending compiled artifact is consumed.
-/
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Sections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FiberField
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocusTensor

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.FieldAmpleness

/-- Positive actual degree-zero cohomology produces an actual nonzero section
morphism of the given module; no chosen section is supplied by the caller. -/
theorem exists_unitHom_ne_zero_of_finrankH0_pos
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (M : X.Modules)
    (h0 : letI : X.Over (Spec (CommRingCat.of k)) := ⟨f⟩; 0 < M.finrankH k 0) :
    ∃ θ : Scheme.Modules.unit X ⟶ M, θ ≠ 0 := by
  letI : X.Over (Spec (CommRingCat.of k)) := ⟨f⟩
  let e := Scheme.Modules.H.unitHomAddEquiv M
  have hv : ∃ z : M.H 0, z ≠ 0 := by
    by_contra! hz
    haveI : Subsingleton (M.H 0) := ⟨fun a b => (hz a).trans (hz b).symm⟩
    exact (Nat.ne_zero_of_lt h0) Module.finrank_zero_of_subsingleton
  obtain ⟨z, hz⟩ := hv
  refine ⟨e.symm z, ?_⟩
  intro h
  exact hz (by simpa using congrArg e h)

/-- Native W07 residue-fibre H0 over a FIELD gives the same actual section.
The unique field residue fibre is compared by W07's real scheme/scalar iso. -/
theorem exists_unitHom_ne_zero_of_hFiber0_pos
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (M : X.Modules) (s : Spec (CommRingCat.of k)) (h0 : 0 < M.hFiber f 0 s) :
    ∃ θ : Scheme.Modules.unit X ⟶ M, θ ≠ 0 := by
  apply exists_unitHom_ne_zero_of_finrankH0_pos f M
  rw [← Scheme.Modules.hFiber_eq_finrankH f M 0 s]
  exact h0

/-- The GIVEN integral-field line with nonzero actual H0 is O(D) for its
CONSTRUCTED effective Cartier zero ideal. The line and isomorphism are retained. -/
theorem exists_effectiveCartier_of_hFiber0_pos
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) [M.IsInvertible]
    (s : Spec (CommRingCat.of k)) (h0 : 0 < M.hFiber f 0 s) :
    ∃ (θ : Scheme.Modules.unit X ⟶ M) (_ : θ ≠ 0)
      (D : X.IdealSheafData) (_ : D.IsInvertible),
      D = θ.zeroLocus ∧ Nonempty (M ≅ D.toModulesᵛ) := by
  obtain ⟨θ, hθ⟩ := exists_unitHom_ne_zero_of_hFiber0_pos f M s h0
  have hD : θ.zeroLocus.IsInvertible := Scheme.Modules.Hom.isInvertible_zeroLocus hθ
  letI := hD.isInvertible_toModules
  obtain ⟨e⟩ := Scheme.Modules.Hom.nonempty_iso_dual_toModules_tensorObj θ hD
  exact ⟨θ, hθ, θ.zeroLocus, hD, rfl, ⟨e ≪≫ ρ_ θ.zeroLocus.toModulesᵛ⟩⟩

/-- Specialization to the actual original-field abelian GROUP object; total
integrality is derived, not a new field-ampleness context hypothesis. -/
theorem abelianVariety_exists_effectiveCartier_of_hFiber0_pos
    {k : Type u} [Field k]
    (A : Grp (Over (Spec (CommRingCat.of k)))) [PkgI2.IsAbelianVariety A]
    (M : A.X.left.Modules) [M.IsInvertible]
    (s : Spec (CommRingCat.of k)) (h0 : 0 < M.hFiber A.X.hom 0 s) :
    ∃ (θ : Scheme.Modules.unit A.X.left ⟶ M) (_ : θ ≠ 0)
      (D : A.X.left.IdealSheafData) (_ : D.IsInvertible),
      D = θ.zeroLocus ∧ Nonempty (M ≅ D.toModulesᵛ) := by
  haveI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  haveI : IsIntegral A.X.left :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.X.hom
  exact exists_effectiveCartier_of_hFiber0_pos A.X.hom M s h0

#print axioms exists_unitHom_ne_zero_of_finrankH0_pos
#print axioms exists_unitHom_ne_zero_of_hFiber0_pos
#print axioms exists_effectiveCartier_of_hFiber0_pos
#print axioms abelianVariety_exists_effectiveCartier_of_hFiber0_pos

end ZInQ.Contrib.CloudR2NOS.FieldAmpleness
