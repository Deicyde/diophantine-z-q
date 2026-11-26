import ZInQKernel.Contrib.OneProof.EllAdic.LiftedFiniteResidueDiagonalV1
import Mathlib.CategoryTheory.Sites.LocallyInjective

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace RC53.EllAdic

universe u

/-- Equality of the two constant residue functions implies equality of their
values after evaluation on any nonempty object. On an empty object the
pro-étale empty cover gives local injectivity instead. -/
theorem liftedResidueConstantDiagonal_locallyInjective (S : Scheme.{u}) (p n : ℕ) :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology S)
      (liftedResidueConstantDiagonal S p n) where
  equalizerSieve_mem {X} x y h := by
    by_cases hx : Nonempty X.unop.left
    · obtain ⟨w⟩ := hx
      have hdown : x.down = y.down :=
        congrArg (fun z : ULift.{u+1} (LocallyConstant X.unop.left (ZMod (p ^ n))) =>
          z.down w) h
      have heq : x = y := ULift.ext hdown
      subst y
      rw [Presheaf.equalizerSieve_self_eq_top]
      exact (Scheme.ProEt.topology S).top_mem X.unop
    · let : IsEmpty X.unop.left := ⟨fun w => hx ⟨w⟩⟩
      exact (Scheme.ProEt.topology S).superset_covering bot_le
        (Scheme.ProEt.bot_mem_topology X.unop)

end RC53.EllAdic
