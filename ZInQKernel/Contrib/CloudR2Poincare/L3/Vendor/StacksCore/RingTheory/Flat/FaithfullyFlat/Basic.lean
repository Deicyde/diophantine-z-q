import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksCore.RingTheory.Flat.FaithfullyFlat.Basic`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-! Stacks 0H7K: existence of a common field extension. Given two field extensions
`E/K` and `F/K`, the quotient of `E ⊗[K] F` by a maximal ideal is a field over which
both `E` and `F` embed compatibly with the structure maps from `K`. The Lean
statement is more general (it asks only for `[Nontrivial (E ⊗[K] F)]`), which is
automatic in the field case via `Module.FaithfullyFlat.lTensor_nontrivial`. -/


universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
#cloudR2Vendor exists_common_extension in

/-- **Stacks Lemma 0H7K**: Given two field extensions E/K and F/K, there exists a common field
extension M/K with K-algebra maps E → M and F → M. (The Lean statement is more general but will
apply where `[Field K] [Field E] [Field F]` by virtue of Mathlib instance
`Module.FaithfullyFlat.lTensor_nontrivial`.) -/

theorem exists_common_extension (K : Type u) (E : Type v) (F : Type w) [CommSemiring K]
    [CommRing E] [CommSemiring F] [Algebra K E] [Algebra K F] [Nontrivial (E ⊗[K] F)] :
    ∃ (M : Type (max v w)) (_ : Field M) (_ : Algebra K M) (_ : Algebra E M) (_ : Algebra F M),
    IsScalarTower K E M ∧ IsScalarTower K F M := by
  let ⟨m, _⟩ := Ideal.exists_maximal (E ⊗[K] F)
  refine ⟨E ⊗[K] F ⧸ m, Ideal.Quotient.field m, ?_, ?_, ?_, ?_, ?_⟩ <;> infer_instance


end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
