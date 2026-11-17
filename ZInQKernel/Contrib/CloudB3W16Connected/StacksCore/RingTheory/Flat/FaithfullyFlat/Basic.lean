/-
Cloud batch 3 W16 H99 port (2026-11-16).
Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b, recovered
StacksCore/RingTheory/Flat/FaithfullyFlat/Basic.lean.
Changes: Import paths moved to CloudB3W16Connected.
Citation attributes/commands and registration imports omitted; mathematical references retained.
The older vendoring notice below is retained as provenance, not a claim that
this additional port is unchanged. See LICENSE and NOTICE.md in this family.
-/
/-
H71 lane04 VENDORED copy (root-default, publication decision 2026-11-14) of `StacksCore.RingTheory.Flat.FaithfullyFlat.Basic`,
from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b (original notices retained below). Original sha256 372e09c425b6fa6bc32545e96143cd1661433d09ad4ac580f3392990e8e84ad3.
Modification notice (2026-11-14): module path ZInQKernel.Contrib.CloudB3W16Connected.StacksCore.RingTheory.Flat.FaithfullyFlat.Basic; 0 import directive rewrite(s) to the
vendored/published module identities; 0 resolved `_c496` family rename(s) of declarations
colliding with the published fork graph; the original package type-inference/printing
options (autoImplicit, relaxedAutoImplicit, maxSynthPendingDepth, pp.unicode.fun) as
explicit `set_option` lines after the imports (diagnostic weak.linter options are left to
the root library). No other change.
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true


/-! Stacks 0H7K: existence of a common field extension. Given two field extensions
`E/K` and `F/K`, the quotient of `E ⊗[K] F` by a maximal ideal is a field over which
both `E` and `F` embed compatibly with the structure maps from `K`. The Lean
statement is more general (it asks only for `[Nontrivial (E ⊗[K] F)]`), which is
automatic in the field case via `Module.FaithfullyFlat.lTensor_nontrivial`. -/

@[expose] public section

universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

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

end
