-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.ChowLemma.ProjectiveEmbedding), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ChowLemma.Graph
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Product

/-!
# Projective embeddings of tuple-image graphs

A finite product of projective spaces admits a Segre embedding. Restricting it
to the scheme-theoretic image of a tuple embeds the graph into one projective
space over the same base.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ChowGraph

variable {coverIndex : Type*} [Finite coverIndex]
  {sourceScheme baseScheme : Scheme.{u}} {baseMap : sourceScheme ⟶ baseScheme}
  {cover : coverIndex → sourceScheme.Opens}
  (closedModels : ∀ index, ProperClosedModel ((cover index).ι ≫ baseMap))

theorem exists_isClosedImmersion_over :
    ∃ (coordinates : Type u) (_ : Finite coordinates) (projectiveEmbedding : ChowGraph closedModels ⟶ ℙ(coordinates; baseScheme)),
      IsClosedImmersion projectiveEmbedding ∧ projectiveEmbedding ≫ ℙ(coordinates; baseScheme) ↘ baseScheme = structureMap closedModels := by
  obtain ⟨coverCard, ⟨immersion⟩⟩ := Finite.exists_equiv_fin coverIndex
  let indexEquiv : coverIndex ≃ ULift.{u} (Fin coverCard) := immersion.trans Equiv.ulift.symm
  obtain ⟨coordinates, hN, projectiveEmbedding, hg⟩ :=
    ProjectiveSpace.exists_isClosedImmersion_pi (fun otherIndex ↦ (closedModels (indexEquiv.symm otherIndex)).coordinates) baseScheme
  let ee : ambient closedModels ≅ ∏ᶜ fun otherIndex ↦ Over.mk (ℙ((closedModels (indexEquiv.symm otherIndex)).coordinates; baseScheme) ↘ baseScheme) :=
    Pi.whiskerEquiv (f := fun index ↦ Over.mk (ℙ((closedModels index).coordinates; baseScheme) ↘ baseScheme))
      (g := fun otherIndex ↦ Over.mk (ℙ((closedModels (indexEquiv.symm otherIndex)).coordinates; baseScheme) ↘ baseScheme)) indexEquiv
      fun index ↦ eqToIso (by rw [Equiv.symm_apply_apply])
  have : IsIso ee.hom.left := inferInstanceAs (IsIso ((Over.forget baseScheme).map ee.hom))
  refine ⟨coordinates, hN, embedding closedModels ≫ (ee.hom ≫ projectiveEmbedding).left, ?_, ?_⟩
  · rw [Over.comp_left]
    infer_instance
  · have witness := Over.w (ee.hom ≫ projectiveEmbedding)
    simp only [Over.mk_hom] at witness
    rw [Category.assoc, witness, structureMap]

end AlgebraicGeometry.ChowGraph
