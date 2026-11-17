/-
H5 Lane5 — actual closed-fibre effectivity seam for closed-section research.
SOURCE ONLY / UNCOMPILED. Native remains held; no source/runtime binding or
whole-type/BinderInfo/Std3 grade is asserted by this file.

This is a thin consumer of ALREADY HELD source primitives, not another Γ,
cohomology-model, divisor-effectivity or special-group-geometry proof:
* lead NativeGeometricSourceInput6063 supplies the actual field-pullback group;
* W07 Fiber/FiberBaseChange/FiberField supply the literal cohomology maps;
* NativeEffectivity b6 supplies the actual nonzero section/Cartier zero ideal.

H and M below are the EXACT constructed stage/group/line witnesses of
OriginalInputPositiveStage. No other line, model, rational point or field is
chosen. The hypotheses here are earlier producer OUTPUTS, not extra premises
of the original NOS telescope. This file does NOT infer ampleness, finite or
closed sections from H0/Euler. The specialized abelian criterion and its DVR
relative-presentation lift remain separate unproved/unbound obligations.
-/
import NativeGeometricSourceInput
import ZInQKernel.Contrib.CloudR2NOS.FieldAmpleness.NativeEffectivity
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FiberBaseChange

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane5.SpecialFibreResearch

/-- The field, group, module and Cartier ideal are literal closed-fibre data.
No field criterion is assumed. This result supplies exactly the nonzero section
and actual native Euler facts the proposed abelian ampleness route would need. -/
theorem effective_and_euler_ne_zero_on_actual_special_fibre
    {C : Type u} [CommRing C] [IsDiscreteValuationRing C]
    (H : Grp (Over (Spec (CommRingCat.of C)))) [PkgI2.IsAbelianScheme H]
    (M : H.X.left.Modules) [M.IsInvertible]
    (h0 : 0 < M.hFiber H.X.hom 0 (IsLocalRing.closedPoint C))
    (hχ : M.eulerCharFiber H.X.hom (IsLocalRing.closedPoint C) ≠ 0) :
    let s := IsLocalRing.closedPoint C
    let k : Type u := (Spec (CommRingCat.of C)).residueField s
    let g := (Spec (CommRingCat.of C)).fromSpecResidueField s
    let Hs := (Over.pullback g).mapGrp.obj H
    let Ms := (Scheme.Modules.pullback (H.X.hom.fiberι s)).obj M
    PkgI2.IsAbelianVariety Hs ∧
      Ms.IsInvertible ∧
      (letI : Hs.X.left.Over (Spec (CommRingCat.of k)) := ⟨Hs.X.hom⟩
       Ms.eulerChar k ≠ 0) ∧
      ∃ (θ : Scheme.Modules.unit Hs.X.left ⟶ Ms) (_ : θ ≠ 0)
        (D : Hs.X.left.IdealSheafData) (_ : D.IsInvertible),
        D = θ.zeroLocus ∧ Nonempty (Ms ≅ D.toModulesᵛ) := by
  dsimp only
  let s := IsLocalRing.closedPoint C
  let k : Type u := (Spec (CommRingCat.of C)).residueField s
  let g := (Spec (CommRingCat.of C)).fromSpecResidueField s
  let Hs := (Over.pullback g).mapGrp.obj H
  let Ms := (Scheme.Modules.pullback (H.X.hom.fiberι s)).obj M
  letI : IsProper H.X.hom := PkgI2.IsAbelianScheme.proper
  letI : PkgI2.IsAbelianVariety Hs :=
    ZInQ.Contrib.CloudR2NOS.FieldAmpleness.NativeGeometricSourceInput.
      field_pullback_isAbelianVariety H g
  letI : Ms.IsInvertible := inferInstance
  have hgs : g.base (IsLocalRing.closedPoint k) = s :=
    Scheme.fromSpecResidueField_apply _ _
  have h0s : 0 < Ms.hFiber Hs.X.hom 0 (IsLocalRing.closedPoint k) := by
    change 0 < ((Scheme.Modules.pullback (pullback.fst H.X.hom g)).obj M).
      hFiber (pullback.snd H.X.hom g) 0 (IsLocalRing.closedPoint k)
    rw [Scheme.Modules.hFiber_pullback_of_isPullback H.X.hom M g
      (pullback.fst H.X.hom g) (pullback.snd H.X.hom g)
      (IsPullback.of_hasPullback H.X.hom g) 0 (IsLocalRing.closedPoint k), hgs]
    exact h0
  have hχs : Ms.eulerCharFiber Hs.X.hom (IsLocalRing.closedPoint k) ≠ 0 := by
    change ((Scheme.Modules.pullback (pullback.fst H.X.hom g)).obj M).
      eulerCharFiber (pullback.snd H.X.hom g) (IsLocalRing.closedPoint k) ≠ 0
    rw [Scheme.Modules.eulerCharFiber_pullback_of_isPullback H.X.hom M g
      (pullback.fst H.X.hom g) (pullback.snd H.X.hom g)
      (IsPullback.of_hasPullback H.X.hom g) (IsLocalRing.closedPoint k), hgs]
    exact hχ
  have hEuler :
      (letI : Hs.X.left.Over (Spec (CommRingCat.of k)) := ⟨Hs.X.hom⟩
       Ms.eulerChar k ≠ 0) := by
    letI : Hs.X.left.Over (Spec (CommRingCat.of k)) := ⟨Hs.X.hom⟩
    rw [← Scheme.Modules.eulerCharFiber_eq_eulerChar Hs.X.hom Ms
      (IsLocalRing.closedPoint k)]
    exact hχs
  obtain ⟨θ, hθ, D, hD, hZero, hMsD⟩ :=
    ZInQ.Contrib.CloudR2NOS.FieldAmpleness.
      abelianVariety_exists_effectiveCartier_of_hFiber0_pos
        Hs Ms (IsLocalRing.closedPoint k) h0s
  exact ⟨inferInstance, inferInstance, hEuler, θ, hθ, D, hD, hZero, hMsD⟩

/-
No `IsAmple`, `FiniteBySections` or `ClosedImmersionBySections` conclusion
occurs here. A different project's ample predicate/Euler characteristic, an
auxiliary fixed very ample bundle, or a reverse application of Serre cannot
supply that conclusion for this actual Ms. Such a bridge needs the actual
abelian nondegenerate-line proof and the correct source/scalar/power maps.
-/

end H5OriginalDVR.Lane5.SpecialFibreResearch
