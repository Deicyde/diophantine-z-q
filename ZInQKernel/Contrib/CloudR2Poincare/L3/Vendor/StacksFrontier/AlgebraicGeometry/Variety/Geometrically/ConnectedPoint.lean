import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedCriterion
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
Only upstream lines [(97, 112)] are retained.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory

open _root_.CategoryTheory
open CategoryTheory
universe u
namespace AlgebraicGeometry
#cloudR2LocalInstances
#cloudR2Vendor geometricallyConnected_of_connectedSpace_of_section in
/-- **Stacks Project, Tag 04KV, rational-point consequence.** A connected scheme
over a field with a rational point is geometrically connected. -/

theorem geometricallyConnected_of_connectedSpace_of_section
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace X] (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    GeometricallyConnected f := by
  have hgc : GeometricallyConnected (𝟙 (Spec (.of k))) := by
    refine ⟨fun K _ y Z fst snd hp ↦ ?_⟩
    let := hp.isIso_snd_of_isIso
    exact (show ObjectProperty Scheme from fun Y ↦ ConnectedSpace Y).prop_of_iso
      (asIso snd).symm inferInstance
  let : GeometricallyConnected (s ≫ f) := hs ▸ hgc
  exact geometricallyConnected_of_comp_of_connectedSpace k s f

end AlgebraicGeometry

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
