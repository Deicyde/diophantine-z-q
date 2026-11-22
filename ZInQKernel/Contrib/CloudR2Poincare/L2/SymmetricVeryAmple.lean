import ZInQKernel.Contrib.CloudR2Poincare.L2.VeryAmpleTrivial
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorEquivalence

/-!
# A symmetric-trivial very ample bundle forces dimension zero

This proves Mumford's ample-bundle contradiction without a tensor-ampleness
Fact. A very ample bundle M has a nonzero section. So does [-1]^*M. If their
tensor product is trivial, the latter section gives a nonzero map M→O, and
proper integrality makes M trivial. Native projective coordinates then imply
that the actual variety is finite over the original field.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj
open Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Tensor-triviality turns a nonzero section of N into a nonzero map M→O_X.
Nonzeroness follows from the faithful tensor equivalence by the actual M. -/
theorem exists_nonzero_map_to_unit_of_tensor_trivial {X : Scheme.{u}}
    (M N : X.Modules) [M.IsInvertible]
    (s : unit X ⟶ N) (hs : s ≠ 0)
    (h : Nonempty (M ⊗ N ≅ unit X)) : ∃ t : M ⟶ unit X, t ≠ 0 := by
  obtain ⟨e⟩ := h
  let t : M ⟶ unit X := (ρ_ M).inv ≫ (M ◁ s) ≫ e.hom
  refine ⟨t, ?_⟩
  intro ht
  have hzero : M ◁ s = 0 := by
    have h' := congrArg (fun f : M ⟶ unit X => (ρ_ M).hom ≫ f ≫ e.inv) ht
    simpa only [t, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id, comp_zero, zero_comp] using h'
  apply hs
  apply (tensorLeft M).map_injective
  change M ◁ s = M ◁ (0 : unit X ⟶ N)
  rw [hzero]
  change 0 = (tensorLeft M).map (0 : unit X ⟶ N)
  exact (Functor.map_zero (tensorLeft M) (unit X) N).symm

/-- A very ample bundle and a globally effective tensor inverse on a proper
integral scheme force dimension zero. -/
theorem dimension_le_zero_of_veryAmple_of_effective_inverse {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] [IsIntegral X]
    (M N : X.Modules) (hM : VeryAmple p M)
    (sN : unit X ⟶ N) (hsN : sN ≠ 0) (htensor : Nonempty (M ⊗ N ≅ unit X)) :
    topologicalKrullDim X ≤ 0 := by
  letI : M.IsInvertible := hM.isInvertible
  obtain ⟨sM, hsM⟩ := hM.exists_nonzero_unit_map
  obtain ⟨t, ht⟩ := exists_nonzero_map_to_unit_of_tensor_trivial M N sN hsN htensor
  exact dimension_le_zero_of_veryAmple_of_trivial p M hM
    (nonempty_iso_unit_of_nonzero_maps p M sM t hsM ht)

/-- Pullback along an automorphism over the original field preserves the
conventional very-ampleness property. -/
theorem VeryAmple.automorphismPullback {X S : Scheme.{u}} {p : X ⟶ S} {M : X.Modules}
    (hM : VeryAmple p M) (f : X ⟶ X) [IsIso f] (hf : f ≫ p = p) :
    VeryAmple p ((Scheme.Modules.pullback f).obj M) := by
  simpa only [hf] using hM.closedRestriction f

/-- **Mumford's contradiction on the actual abelian variety.** If a very ample
M has trivial M⊗[-1]^*M, the actual variety has dimension at most zero.
No represented Picard scheme, complement, or characteristic assumption is used. -/
theorem dimension_le_zero_of_symmetrized_veryAmple_trivial
    {k : Type u} [Field k] (A : PkgI3.AbVar k) (M : A.X.left.Modules)
    (hM : VeryAmple A.X.hom M)
    (htrivial : Nonempty
      (M ⊗ (Scheme.Modules.pullback ι[A.X].left).obj M ≅ unit A.X.left)) :
    A.dim ≤ 0 := by
  letI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  letI : IsIso ι[A.X].left := by
    change IsIso ((Over.forget (Spec (.of k))).map ι[A.X])
    infer_instance
  have hN : VeryAmple A.X.hom ((Scheme.Modules.pullback ι[A.X].left).obj M) :=
    hM.automorphismPullback ι[A.X].left (Over.w ι[A.X])
  obtain ⟨sN, hsN⟩ := hN.exists_nonzero_unit_map
  exact dimension_le_zero_of_veryAmple_of_effective_inverse A.X.hom M
    ((Scheme.Modules.pullback ι[A.X].left).obj M) hM sN hsN htrivial

/-- Thus no positive-dimensional actual abelian variety admits a symmetric-
trivial very ample bundle. -/
theorem symmetrized_veryAmple_nontrivial_of_positive_dimension
    {k : Type u} [Field k] (A : PkgI3.AbVar k) (hA : 0 < A.dim)
    (M : A.X.left.Modules) (hM : VeryAmple A.X.hom M) :
    ¬ Nonempty (M ⊗ (Scheme.Modules.pullback ι[A.X].left).obj M ≅ unit A.X.left) := by
  intro htrivial
  exact not_lt_of_ge (dimension_le_zero_of_symmetrized_veryAmple_trivial A M hM htrivial) hA

end ZInQ.Contrib.CloudR2Poincare.L2
