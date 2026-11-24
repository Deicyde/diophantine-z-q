import ZInQKernel.Contrib.CloudR2Poincare.L3.B1EdgeComplex
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-!
# Native edge Leray, without a caller-supplied degeneration premise

The comparison is built from the actual injective resolution, higher-direct-
image/homology comparison, native cycle quotients and native H-zero map used by
B2Leray. It does not select an arbitrary equivalence from Nonempty. The actual
pushforward of injectives is flasque and hence Γ-acyclic for every morphism;
lower direct-image vanishing supplies the only other input. Thus no geometric
qcqs/separated/QC hypothesis is used or silently dropped.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits

namespace ZInQ.Contrib.CloudR2Poincare.L3.NativeEdge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u
variable {X Y : Scheme.{u}}

/-- Lower direct-image vanishing gives acyclicity of precisely the lower native
homology sheaves of the pushed-forward actual injective resolution. -/
theorem pushforwardHomologyAcyclicBelow (f : X ⟶ Y) (F : X.Modules)
    (I : InjectiveResolution F) (q : ℕ)
    (hzero : ∀ j : ℕ, j < q → IsZero ((Scheme.Modules.higherDirectImage f j).obj F)) :
    ∀ j : ℕ, j < q → ∀ m : ℕ,
      Subsingleton ((HomologicalComplex.homology
        (((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj I.cocomplex) j).H
          (m + 1)) := by
  intro j hj m
  haveI : Subsingleton ((((Scheme.Modules.pushforward f).rightDerived j).obj F).H (m + 1)) :=
    subsingleton_H_of_isZero ((Scheme.Modules.higherDirectImage f j).obj F) (hzero j hj)
      (m + 1)
  exact (Scheme.Modules.H.mapLinearEquiv
    (I.isoRightDerivedObj (Scheme.Modules.pushforward f) j).symm
      (m + 1)).injective.subsingleton

/-- The explicit native resolution/cycles edge map, oriented from higher direct-
image sections to source cohomology, matching the published Sections convention. -/
def resolutionEdgeSectionsAddEquiv (f : X ⟶ Y) (F : X.Modules)
    (I : InjectiveResolution F) (n : ℕ)
    (hzero : ∀ j : ℕ, j < n + 1 → IsZero ((Scheme.Modules.higherDirectImage f j).obj F)) :
    Γ((Scheme.Modules.higherDirectImage f (n + 1)).obj F, ⊤) ≃+ F.H (n + 1) := by
  let L : CochainComplex Y.Modules ℕ :=
    ((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj I.cocomplex
  have hL : ∀ j m : ℕ, Subsingleton ((L.X j).H (m + 1)) := fun j m =>
    Scheme.Modules.subsingleton_H_pushforward_of_injective f (I.cocomplex.X j) m
  have hH : ∀ j : ℕ, j < n + 1 → ∀ m : ℕ,
      Subsingleton ((L.homology j).H (m + 1)) :=
    pushforwardHomologyAcyclicBelow f F I (n + 1) hzero
  exact (Scheme.Modules.appTopAddEquiv
      (I.isoRightDerivedObj (Scheme.Modules.pushforward f) (n + 1))).trans
    ((homologySectionsEdgeAddEquiv L hL n hH).trans
      ((Scheme.Modules.cyclesQuotientAddEquiv L n).trans
        ((AddEquiv.refl (Scheme.Modules.sectionsCycles I.cocomplex n ⧸
            Scheme.Modules.sectionsBoundaries I.cocomplex n)).trans
          ((Scheme.Modules.cyclesQuotientAddEquiv I.cocomplex n).symm.trans
            ((Scheme.Modules.H.cyclesZeroSuccAddEquiv I.cocomplex
              I.cocomplex_exactAt_succ
              (fun _ m => Scheme.Modules.subsingleton_H_of_injective _ m) n).symm.trans
              (Scheme.Modules.H.mapAddEquiv I.isoCyclesZero.symm (n + 1)))))))

end ZInQ.Contrib.CloudR2Poincare.L3.NativeEdge

namespace ZInQ.Contrib.CloudR2Poincare.L3

universe u

/-- Canonical native edge Leray. Only actual higher direct images strictly below
q are zero; no acyclicity of R^q f_*F and no Leray Fact is required. -/
def native_edge_leray_addEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (q : ℕ)
    (hzero : ∀ j : ℕ, j < q → IsZero ((Scheme.Modules.higherDirectImage f j).obj F)) :
    F.H q ≃+ (((Scheme.Modules.higherDirectImage f q).obj F).H 0) := by
  cases q with
  | zero =>
    exact ((Scheme.Modules.H.zeroLinearEquiv
      ((Scheme.Modules.higherDirectImage f 0).obj F)).toAddEquiv.trans
      (Scheme.Modules.sectionsHigherDirectImageZeroAddEquiv f F)).symm
  | succ n =>
    exact ((Scheme.Modules.H.zeroLinearEquiv
      ((Scheme.Modules.higherDirectImage f (n + 1)).obj F)).toAddEquiv.trans
      (NativeEdge.resolutionEdgeSectionsAddEquiv f F (injectiveResolution F) n hzero)).symm

end ZInQ.Contrib.CloudR2Poincare.L3
