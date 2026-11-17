-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Modules.Discrete), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeGenerator
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Line bundles on discrete schemes

Local generators on the one-point opens glue to a global generator. Thus every invertible
module sheaf on a discrete scheme is trivial.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [DiscreteTopology X]

/-- Every line bundle on a discrete scheme is isomorphic to the structure module. -/
theorem nonempty_iso_unit_of_discrete (M : X.Modules) [M.IsInvertible] :
    Nonempty (M ≅ unit X) := by
  classical
  let U (point : X) : X.Opens := ⟨{point}, isOpen_discrete _⟩
  have localGenerator (point : X) : ∃ sectionValue : Γ(M, U point),
      IsFreeGenerator sectionValue := by
    obtain ⟨V, membership, ⟨trivialization⟩⟩ := exists_mem_over_iso_unit M point
    obtain ⟨sectionValue, generator⟩ := exists_isFreeGenerator_of_iso trivialization
    have inclusion : U point ≤ V := by
      intro otherPoint equality
      change otherPoint = point at equality
      exact equality ▸ membership
    exact ⟨M.presheaf.map (homOfLE inclusion).op sectionValue, generator.map inclusion⟩
  choose sectionValue generator using localGenerator
  let F : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  have covers : (⊤ : X.Opens) ≤ ⨆ point, U point := fun point _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨point, rfl⟩
  obtain ⟨globalSection, restriction, -⟩ := F.existsUnique_gluing' U ⊤
    (fun _ ↦ homOfLE le_top) covers sectionValue fun point otherPoint ↦ by
      by_cases equality : point = otherPoint
      · subst otherPoint
        rfl
      · have emptyIntersection : U point ⊓ U otherPoint = ⊥ := by
          apply le_antisymm _ bot_le
          intro member membership
          exact False.elim (equality (membership.1.symm.trans membership.2))
        have := AddCommGrpCat.subsingleton_of_isZero
          (TopCat.Sheaf.isTerminalOfEqEmpty F emptyIntersection).isZero
        exact Subsingleton.elim _ _
  have restriction' (point : X) :
      M.presheaf.map (homOfLE (le_top : U point ≤ ⊤)).op globalSection =
        sectionValue point := restriction point
  let morphism := homOfGlobalSection M globalSection
  have : IsIso morphism := isIso_of_isFreeGenerator morphism fun point ↦
    ⟨U point, (1 : Γ(X, U point)), rfl, isFreeGenerator_one _, by
      simpa only [morphism, homOfGlobalSection_app_one, restriction' point] using generator point⟩
  exact ⟨(asIso morphism).symm⟩

end AlgebraicGeometry.Scheme.Modules
