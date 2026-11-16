-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant.Opens), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Scheme-theoretically dense open subschemes

An open that is scheme-theoretically dense remains dense in every intermediate open.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {ambientScheme : Scheme.{u}}

/-- A scheme-theoretically dense open remains dense in any intermediate open. -/
theorem IsSchemeTheoreticallyDominant.homOfLE {smallerOpen largerOpen : ambientScheme.Opens} (inclusion : smallerOpen ≤ largerOpen)
    [QuasiCompact smallerOpen.ι] [IsSchemeTheoreticallyDominant smallerOpen.ι] :
    IsSchemeTheoreticallyDominant (ambientScheme.homOfLE inclusion) := by
  have dense_inclusion : IsSchemeTheoreticallyDominant (ambientScheme.homOfLE (inf_le_right : smallerOpen ⊓ largerOpen ≤ largerOpen)) :=
    .of_isPullback (isPullback_opens_inf smallerOpen largerOpen)
  have factorization : ambientScheme.homOfLE inclusion =
      (ambientScheme.isoOfEq (inf_eq_left.mpr inclusion)).inv ≫ ambientScheme.homOfLE (inf_le_right : smallerOpen ⊓ largerOpen ≤ largerOpen) := by
    rw [← cancel_mono largerOpen.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι,
      Scheme.isoOfEq_inv_ι]
  rw [factorization]
  infer_instance

end AlgebraicGeometry
