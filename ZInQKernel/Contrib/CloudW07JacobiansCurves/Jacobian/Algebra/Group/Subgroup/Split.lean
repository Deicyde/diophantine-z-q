-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.Algebra.Group.Subgroup.Split), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Splitting a commutative group along a retraction

A homomorphism from a commutative group with a right inverse decomposes its
domain as the product of its codomain and its kernel.
-/

namespace MonoidHom

variable {source target : Type*} [CommGroup source] [Group target]

/-- A split homomorphism decomposes a commutative group into its target and its kernel. -/
def prodKerEquivOfLeftInverse (retraction : source →* target) (sectionHom : target →* source)
    (leftInverse : Function.LeftInverse retraction sectionHom) : source ≃* target × retraction.ker where
  toFun element :=
    (retraction element, ⟨element * (sectionHom (retraction element))⁻¹, by
      simp [mem_ker, leftInverse (retraction element)]⟩)
  invFun pair := sectionHom pair.1 * pair.2
  left_inv element := by simp
  right_inv pair := by
    have kernel : retraction pair.2 = 1 := pair.2.2
    ext
    · simp [leftInverse pair.1, kernel]
    · simp [leftInverse pair.1, kernel]
  map_mul' firstElement secondElement := by
    ext
    · simp
    · simp only [map_mul, mul_inv, Subgroup.coe_mul, Prod.snd_mul]
      exact mul_mul_mul_comm _ _ _ _

/-- The first component of the splitting is the retraction. -/
@[simp]
lemma prodKerEquivOfLeftInverse_apply_fst (retraction : source →* target)
    (sectionHom : target →* source) (leftInverse : Function.LeftInverse retraction sectionHom)
    (element : source) :
    (prodKerEquivOfLeftInverse retraction sectionHom leftInverse element).1 = retraction element :=
  rfl

/-- The second component removes the contribution from the split target. -/
@[simp]
lemma coe_prodKerEquivOfLeftInverse_apply_snd (retraction : source →* target)
    (sectionHom : target →* source) (leftInverse : Function.LeftInverse retraction sectionHom)
    (element : source) :
    ((prodKerEquivOfLeftInverse retraction sectionHom leftInverse element).2 : source) =
      element * (sectionHom (retraction element))⁻¹ :=
  rfl

/-- The inverse splitting multiplies the lifted target element by the kernel element. -/
@[simp]
lemma prodKerEquivOfLeftInverse_symm_apply (retraction : source →* target)
    (sectionHom : target →* source) (leftInverse : Function.LeftInverse retraction sectionHom)
    (pair : target × retraction.ker) :
    (prodKerEquivOfLeftInverse retraction sectionHom leftInverse).symm pair = sectionHom pair.1 * pair.2 :=
  rfl

end MonoidHom
