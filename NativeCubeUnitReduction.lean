/-
H5 original-input Step2 / GM7: native field-unit and tensor-factor reduction.
Copyright (c) 2026 H5 lane2 contributors. Apache-2.0.

NEW Source-only / UNCOMPILED. No Native permission or current kernel grade.
This supplies only the elementary native reductions needed AFTER the genuine
H71 cube relation has been mapped into this native context. It is NOT I5a,
I5b, a proof of the cube, or an added cube/square Fact or transport factory.

Named pending dependency: the already held
StacksFrontier.AlgebraicGeometry.Cube.TheoremOfTheCube, 35548B,
SHA3b509d6839900fc0d5274b5c35eb98f98fe01bfc35e62868e512af178f281dbc,
full Source read under the Task-A d1346f11/86d27970 gate. That body is not
copied, reproved, compiled, or silently identified with native W07 tensor,
invertibility, pullback or dual. Its native compatibility remains an exact gap.

The field may have ANY characteristic; the scheme universe is symbolic u.
There is no abelian-variety dimension restriction, introduced line/model,
Picard-class premise or replacement of the original special-fibre inputs.
Existing W07 c4254cce LICENSE/NOTICE and primitive Sources are unchanged.
-/
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeGenerator
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorPower

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.NativeCubeUnitReduction

/-- A native invertible module on Spec of ANY field is trivial. The proof
uses an actual global free generator: an open containing the unique point
is top. No Picard/rank/trivial-line hypothesis is supplied by a caller. -/
theorem nonempty_iso_unit_on_spec_field
    {K : Type u} [Field K]
    (N : (Spec (CommRingCat.of K)).Modules) [N.IsInvertible] :
    Nonempty (N ≅ Scheme.Modules.unit (Spec (CommRingCat.of K))) := by
  obtain ⟨U, hxU, _, s, hs⟩ := Scheme.Modules.exists_isFreeGenerator N
    (x := IsLocalRing.closedPoint K) (W := ⊤) trivial
  have hU : U.1 = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    simpa only [hy] using hxU
  have hgen : ∃ s : Γ(N, U.1), Scheme.Modules.IsFreeGenerator s := ⟨s, hs⟩
  rw [hU] at hgen
  obtain ⟨s0, hs0⟩ := hgen
  let φ := Scheme.Modules.homOfGlobalSection N s0
  have hφ : IsIso φ := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro V
    apply (ConcreteCategory.isIso_iff_bijective (φ.app V)).mpr
    change Function.Bijective (fun r : Γ(Spec (CommRingCat.of K), V) => φ.app V r)
    simpa only [φ, Scheme.Modules.homOfGlobalSection_app] using hs0 V le_top
  letI := hφ
  exact ⟨(asIso φ).symm⟩

/-- An actual map factoring through a field-valued point pulls a native
line back to the native unit, by the literal pullback-composition/unit maps.
This is the constant-factor reduction in the (id,x,y) cube restriction. -/
theorem nonempty_pullback_iso_unit_through_field_point
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ Y)
    (N : Y.Modules) [N.IsInvertible] :
    Nonempty ((Scheme.Modules.pullback (f ≫ x)).obj N ≅ Scheme.Modules.unit X) := by
  obtain ⟨e⟩ := nonempty_iso_unit_on_spec_field ((Scheme.Modules.pullback x).obj N)
  exact ⟨(Scheme.Modules.pullbackComp f x).symm.app N ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫ Scheme.Modules.pullbackObjUnitIso f⟩

/-- Pure native categorical reduction of an ACTUAL isomorphism once its
three extra factors have ACTUAL unit isomorphisms. This is not a cube premise,
not a theorem on A, and does not produce the missing cube-restriction iso. -/
def remove_two_left_unit_factors_one_right
    {X : Scheme.{u}} (A B C D U V W : X.Modules)
    (e : ((A ⊗ B) ⊗ U) ⊗ V ≅ (C ⊗ D) ⊗ W)
    (eU : U ≅ Scheme.Modules.unit X)
    (eV : V ≅ Scheme.Modules.unit X)
    (eW : W ≅ Scheme.Modules.unit X) : A ⊗ B ≅ C ⊗ D :=
  (ρ_ (A ⊗ B)).symm ≪≫ whiskerLeftIso (A ⊗ B) eU.symm ≪≫
    (ρ_ ((A ⊗ B) ⊗ U)).symm ≪≫ whiskerLeftIso ((A ⊗ B) ⊗ U) eV.symm ≪≫
    e ≪≫ whiskerLeftIso (C ⊗ D) eW ≪≫ ρ_ (C ⊗ D)

end H5OriginalDVR.Lane2.NativeCubeUnitReduction
