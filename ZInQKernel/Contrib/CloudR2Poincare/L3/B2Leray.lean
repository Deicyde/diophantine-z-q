import ZInQKernel.Contrib.CloudR2Poincare.L3.B2Interface
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-!
# Native Leray degeneration from acyclic direct-image cohomology

Source credit: the constructive comparison is adapted from published W07
`Cohomology/DirectImage/Sections.lean:60–76`, vendored from Jacobian-Challenge
c4254cce15b3e284a0a3ae1d73936f2ee195d272, Apache-2.0 (W07 LICENSE/NOTICE).
Prominent change notice: affine-base vanishing of the cohomology sheaves is
replaced by the EXPLICIT acyclicity hypothesis of NativeLerayDegeneration.
The existing acyclic-resolution proof then applies to arbitrary target schemes.
No Leray/spectral-sequence Fact is assumed.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits

namespace ZInQ.Contrib.CloudR2Poincare.L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u

/-- Constructive native degeneration for any morphism once the actual higher
cohomology of every direct image vanishes. No affine-target assumption. -/
theorem nonempty_native_leray_addEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules)
    (hR : ∀ (j p : ℕ), 0 < p →
      Subsingleton (((Scheme.Modules.higherDirectImage f j).obj F).H p)) (i : ℕ) :
    Nonempty (F.H i ≃+ (((Scheme.Modules.higherDirectImage f i).obj F).H 0)) := by
  let I := injectiveResolution F
  cases i with
  | zero =>
    exact ⟨((Scheme.Modules.H.zeroLinearEquiv
      ((Scheme.Modules.higherDirectImage f 0).obj F)).toAddEquiv.trans
      (Scheme.Modules.sectionsHigherDirectImageZeroAddEquiv f F)).symm⟩
  | succ n =>
    let L := ((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj I.cocomplex
    have hL : ∀ j m : ℕ, Subsingleton ((L.X j).H (m + 1)) := fun j m =>
      Scheme.Modules.subsingleton_H_pushforward_of_injective f (I.cocomplex.X j) m
    have hHom : ∀ j m : ℕ, Subsingleton ((L.homology j).H (m + 1)) := by
      intro j m
      haveI : Subsingleton ((((Scheme.Modules.pushforward f).rightDerived j).obj F).H (m + 1)) :=
        hR j (m + 1) (by omega)
      exact (Scheme.Modules.H.mapLinearEquiv
        (I.isoRightDerivedObj (Scheme.Modules.pushforward f) j).symm (m + 1)).injective.subsingleton
    let e : Γ((Scheme.Modules.higherDirectImage f (n + 1)).obj F, ⊤) ≃+ F.H (n + 1) :=
      (Scheme.Modules.appTopAddEquiv (I.isoRightDerivedObj (Scheme.Modules.pushforward f) (n + 1))).trans
        ((Scheme.Modules.homologySectionsAddEquiv L hL hHom n).trans
          ((Scheme.Modules.cyclesQuotientAddEquiv L n).trans
            ((AddEquiv.refl (Scheme.Modules.sectionsCycles I.cocomplex n ⧸
                Scheme.Modules.sectionsBoundaries I.cocomplex n)).trans
              ((Scheme.Modules.cyclesQuotientAddEquiv I.cocomplex n).symm.trans
                ((Scheme.Modules.H.cyclesZeroSuccAddEquiv I.cocomplex I.cocomplex_exactAt_succ
                  (fun _ m => Scheme.Modules.subsingleton_H_of_injective _ m) n).symm.trans
                  (Scheme.Modules.H.mapAddEquiv I.isoCyclesZero.symm (n + 1)))))))
    exact ⟨((Scheme.Modules.H.zeroLinearEquiv
      ((Scheme.Modules.higherDirectImage f (n + 1)).obj F)).toAddEquiv.trans e).symm⟩

/-- The agreed ONE labelled Leray input is now proved constructively. -/
theorem NativeLerayDegeneration_proof : NativeLerayDegeneration.{u} := by
  intro k _ B F _ f _ hR i
  exact nonempty_native_leray_addEquiv f F hR i

end ZInQ.Contrib.CloudR2Poincare.L3
