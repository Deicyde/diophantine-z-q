import ZInQKernel.Contrib.OneProof.EllAdic.CountableTensorRefinement
import ZInQKernel.Contrib.OneProof.EllAdic.FaithfullyFlatDirectLimitNatV1
import Mathlib.RingTheory.RingHom.FaithfullyFlat

set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct

namespace RC53.EllAdic

universe u

open CountableTensorRefinement

variable {A : Type u} [CommRing A] (C : ℕ → CommAlgCat.{u} A)

/-- Each literal prefix tensor product is faithfully flat over the original
base when all factors are. The scalar tower uses the left tensor inclusion. -/
theorem faithfullyFlat_tensorPrefix (h : ∀ n, Module.FaithfullyFlat A (C n)) :
    ∀ n, Module.FaithfullyFlat A (stage C n) := by
  intro n
  induction n with
  | zero =>
      change Module.FaithfullyFlat A A
      exact Module.FaithfullyFlat.self A
  | succ n ih =>
      change Module.FaithfullyFlat A (stage C n ⊗[A] C n)
      let : Module.FaithfullyFlat A (stage C n) := ih
      let : Module.FaithfullyFlat A (C n) := h n
      exact Module.FaithfullyFlat.trans A (stage C n) (stage C n ⊗[A] C n)

/-- Faithful flatness on the actual tensor refinement colimit: the finite
factors map to this same algebra by `factorToLimit`. -/
theorem faithfullyFlat_tensorRefinement (h : ∀ n, Module.FaithfullyFlat A (C n)) :
    (algebraMap A (limit C)).FaithfullyFlat := by
  apply RingHom.faithfullyFlat_algebraMap_iff.mpr
  change Module.FaithfullyFlat A (LimitType C)
  exact faithfullyFlat_directLimit_nat (StageType C) (transition C) (faithfullyFlat_tensorPrefix C h)

end RC53.EllAdic
