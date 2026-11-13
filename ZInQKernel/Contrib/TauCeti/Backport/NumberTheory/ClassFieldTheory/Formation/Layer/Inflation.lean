/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.Formation.Layer.Inflation), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.Layer.Inflation`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.Layer.Inflation
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.Character
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.CoefficientMap
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.Conjugation
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.Restriction
public import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
import ZInQKernel.Contrib.TauCeti.GroupTheory.GroupAction.FixedPoints
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Colimit
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.DegreeTwoDescent
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso.Basic
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Transgression
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality
import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

public section
noncomputable section

open _root_.groupCohomology ContCohomology
namespace TauCeti.ClassFieldTheory.NormalLayer

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (L : NormalLayer G) {F : Formation G}
  {M : Type} [AddCommGroup M] [DistribMulAction G M] (e : M ≃+ F.toRep.V)
  (he : ∀ (g : G) (x : M), e (g • x) = F.toRep.ρ g (e x))
variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- **The inflated Artin character cup is the carry class.** For an element `a'` of the ground
level `A^U` of a layer and a character `χ'` of its abelianized Galois group, read on `U` as `ψ`, the
inflation to `U` of the class `a' ∪ δχ'` of the character formula is the class of the carry cocycle
of `ψ` and of `a'`, read as an invariant `a` of `U` in `M`. -/
theorem explicitInfl2_artinCharacterCup (a' : F.level L.ground)
    (χ' : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ))
    (ψ : Additive L.ground.toSubgroup →+ AddCircle (1 : ℚ))
    (hψ : IsOpen (ψ.ker : Set (Additive L.ground.toSubgroup)))
    (hψχ : ∀ u : L.ground.toSubgroup,
      ψ (.ofMul u) = χ' (.ofMul (Abelianization.of (u : L.Gal))))
    (a : H0 L.ground.toSubgroup M) (ha : e a = a') :
    L.explicitInfl2 e he (L.artinCharacterCup F a' χ') =
      (characterCarryCocycle ψ hψ a : H2 L.ground.toSubgroup M) := by
  -- `ψ` is `χ'` read on `U` through `U → U ⧸ V`.
  have hψ' : ψ = (χ'.comp Abelianization.of.toAdditive).comp
      (QuotientGroup.mk' L.relativeTop : L.ground.toSubgroup →* L.Gal).toAdditive :=
    AddMonoidHom.ext fun u ↦ hψχ u.toMul
  rw [← LinearEquiv.apply_symm_apply (L.groundLevelEquiv F) a',
    artinCharacterCup_groundLevelEquiv_eq_H2π, explicitInfl2_H2π]
  congr 1
  refine Subtype.ext (funext fun ⟨u, v⟩ ↦ ?_)
  rw [inflCocycle2_apply, TauCeti.groupCohomology.characterCarryCocycles₂_apply,
    characterCarryCocycle_apply]
  simp only [AddSubgroupClass.coe_zsmul, map_zsmul, hψ', characterCarry_comp]
  refine congrArg₂ (· • ·) rfl ((AddEquiv.symm_apply_eq _).2 ?_)
  exact (groundLevelEquiv_symm_apply_coe _ _ a').trans ha.symm

end TauCeti.ClassFieldTheory.NormalLayer

end
end
