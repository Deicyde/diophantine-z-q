import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.FieldTheory.Separable.Defs
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.FieldTheory.Separable.PerfectField`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Extensions of a perfect field are separable

Every field extension of a perfect field is separable in the sense of
`Algebra.IsSeparableExtension`, transcendental extensions included: a subextension of finite type
has a transcendence basis over which it is separably generated.

## Main results

* `Algebra.isSeparableExtension_of_perfectField`: every extension of a perfect field is separable.
-/
#cloudR2Vendor Algebra.isSeparableExtension_of_perfectField in


/-- Every extension of a perfect field is separable in the sense of
`Algebra.IsSeparableExtension`: each of its subextensions of finite type is separably generated. -/
lemma Algebra.isSeparableExtension_of_perfectField (k K : Type*) [Field k] [Field K]
    [Algebra k K] [PerfectField k] : Algebra.IsSeparableExtension k K where
  isSeparablyGenerated K' := by
    intro _
    obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K'
    exact ⟨(s : Set K'), hs, H⟩


end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
