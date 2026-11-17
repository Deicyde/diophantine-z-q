/-
Copyright (c) 2026 W17 contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ZInQKernel.Contrib.CloudB3W17ProperCompact.ChowSurjective
import ZInQKernel.Contrib.CloudB3W17ProperCompact.ProjBridge

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace W17ProperCompact

/-- An integral proper scheme has a proper surjective cover with a closed embedding
in the actual terminal-base-change definition of projective space. -/
theorem exists_native_projective_chow_cover {R : Type u} [CommRing R] [IsNoetherianRing R]
    (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [IsIntegral X.left] :
    ∃ (n : ℕ) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ X)
      (i : Y ⟶ Over.mk
        (pullback.fst (terminal.from (Spec (CommRingCat.of R)))
          (terminal.from
            (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)))))),
      IsProper p.left ∧ Surjective p.left ∧ IsClosedImmersion i.left := by
  obtain ⟨D, hD⟩ := exists_surjective_chowDatumProj X.hom
  let Y : Over (Spec (CommRingCat.of R)) := Over.mk (D.p ≫ X.hom)
  let p : Y ⟶ X := Over.homMk D.p rfl
  let e := projSpaceOverIsoTerminal R D.Nd
  let i₀ : Y ⟶ Over.mk (ProjSpace.π R D.Nd) := Over.homMk D.ιN D.hoverN
  let i : Y ⟶ _ := i₀ ≫ e.hom
  have : IsIso e.hom.left :=
    (Functor.map_isIso (Over.forget (Spec (CommRingCat.of R))) e.hom :)
  refine ⟨D.Nd, Y, p, i, D.hp_proper, hD, ?_⟩
  change IsClosedImmersion (D.ιN ≫ e.hom.left)
  infer_instance

end W17ProperCompact
