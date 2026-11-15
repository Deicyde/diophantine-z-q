-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.RingTheory.GradedAlgebra.HomogeneousLocalization.Fractions), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Powers of fractions in homogeneous localization

Taking a power multiplies both the denominator exponent and the homogeneous degree.
The grading can take values in any family of additive subgroups.
-/

set_option backward.isDefEq.respectTransparency false

namespace HomogeneousLocalization

variable {gradedPieces gradedRing : Type*} [CommRing gradedRing]
  [SetLike gradedPieces gradedRing] [AddSubgroupClass gradedPieces gradedRing]
  (grading : ℕ → gradedPieces) [GradedRing grading]
  {denominator : gradedRing} {degree : ℕ}

lemma Away.mk_pow (homogeneous : denominator ∈ grading degree) (exponent : ℕ)
    (numerator : gradedRing) (numeratorHomogeneous : numerator ∈ grading (exponent • degree))
    (power : ℕ) :
    (Away.mk grading homogeneous exponent numerator numeratorHomogeneous) ^ power =
      Away.mk grading homogeneous (power * exponent) (numerator ^ power)
        (mul_smul power exponent degree ▸ SetLike.pow_mem_graded power numeratorHomogeneous) := by
  apply val_injective
  rw [val_pow, Away.val_mk, Away.val_mk, Localization.mk_pow]
  congr 1
  exact Subtype.ext (by rw [SubmonoidClass.coe_pow, ← pow_mul, mul_comm])

end HomogeneousLocalization
