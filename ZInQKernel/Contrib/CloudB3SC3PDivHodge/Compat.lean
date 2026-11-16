/-
Compatibility lemma for the port of Anthropic FLT (commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Lean 4.33.1,
Mathlib db584cd6) to Lean 4.35.0 / Mathlib v4.35.0 (see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md).

In Mathlib db584cd6, `TensorProduct.induction_on` took a `zero` case and was an eliminator (`@[elab_as_elim]`).
Mathlib v4.35.0 keeps it only as a deprecated theorem without the eliminator attribute (the eliminator is now
`TensorProduct.inductionOn`, without the `zero` case). `TensorProduct.induction_on_of_zero` restores the upstream
statement and attribute, proved from Mathlib's `TensorProduct.inductionOn`; ported proofs that used
`TensorProduct.induction_on` as an eliminator call it instead (each site is marked `-- [port]`).
-/
import Mathlib.LinearAlgebra.TensorProduct.Defs

namespace TensorProduct

variable {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

/-- The induction principle of `M ⊗[R] N` with a `zero` case, as an eliminator (the form of
`TensorProduct.induction_on` in Mathlib db584cd6). -/
@[elab_as_elim]
protected theorem induction_on_of_zero {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (zero : motive 0)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.inductionOn z tmul add

end TensorProduct
