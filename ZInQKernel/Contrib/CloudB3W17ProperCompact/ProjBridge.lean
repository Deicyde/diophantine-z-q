/-
Copyright (c) 2026 W17 contributors.
Released under Apache 2.0 license as described in the file LICENSE.

The graded-polynomial base-change square is imported from the existing W02 port
of anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. The target pullback is the actual native
Hodge projective-space definition at 2ead713179628a3c738197d5996f51c8a9c886ac.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_isPullback_map
import Mathlib.Algebra.Field.ULift

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace W17ProperCompact

/-- FLT projective space over `R` is the base change of integral projective space.
The isomorphism preserves the structure morphism to `Spec R`. -/
def projSpaceOverIsoTerminal (R : Type u) [CommRing R] (n : ℕ) :
    Over.mk (ProjSpace.π R n) ≅
      Over.mk
        (pullback.fst (terminal.from (Spec (CommRingCat.of R)))
          (terminal.from
            (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))))) := by
  letI : Algebra (ULift.{u} ℤ) R :=
    ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom).toAlgebra
  have h :=
    (P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.solution (ULift.{u} ℤ) R n).flip
  have : IsIso (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal _
  let e : Spec (CommRingCat.of (ULift.{u} ℤ)) ≅ ⊤_ Scheme.{u} :=
    asIso (terminal.from _)
  have hp : IsPullback (ProjSpace.π R n) (ProjSpace.map (ULift.{u} ℤ) R n)
      (terminal.from (Spec (CommRingCat.of R)))
      (terminal.from
        (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)))) := by
    exact h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
      (by simp) (by simp) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  exact hp.isoOverPullback

/-- The scheme component of the bridge has the expected structure-map equation. -/
theorem projSpaceOverIsoTerminal_hom_comp (R : Type u) [CommRing R] (n : ℕ) :
    (projSpaceOverIsoTerminal R n).hom.left ≫
      pullback.fst (terminal.from (Spec (CommRingCat.of R)))
        (terminal.from
          (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)))) =
      ProjSpace.π R n :=
  Over.w (projSpaceOverIsoTerminal R n).hom

end W17ProperCompact
