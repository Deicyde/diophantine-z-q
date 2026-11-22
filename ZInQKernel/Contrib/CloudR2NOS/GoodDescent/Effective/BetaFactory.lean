/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

CONSTRUCT the actual local-DVR stage and its local, injective original
stage-leg factor β. LocalStage supplies stage geometry, BetaProperties
proves locality/injectivity from the actual equations. No raw-stage
injection, stage-GC premise, or ind-étaleness B_s → P is assumed.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.BetaProperties

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open IsLocalRing CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open OrdinaryStages

/-- The factor through the actual point-selected stage is local and
    injective, DERIVED from the original ordinary residue point and the
    nonzero original O-uniformizer in P. O → P injectivity is provided by
    the original same-closure comap, not injectivity of the raw stage leg. -/
theorem exists_localStage_factor_properties
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {P : Type u} [CommRing P] [IsDomain P] [IsLocalRing P] [Algebra O P]
    (hOP : Function.Injective (algebraMap O P))
    (e : ResidueField O ≃+* ResidueField P)
    (he : ∀ r : O, e (residue O r) = residue P (algebraMap O P r))
    (B : Type u) [CommRing B] [Algebra O B] [Algebra.Etale O B] (ι : B →ₐ[O] P) :
    ∃ s : B, IsUnit (ι s) ∧
      IsLocalization.AtPrime (Localization.Away s) ((maximalIdeal P).comap ι.toRingHom) ∧
      ∃ (_ : IsLocalRing (Localization.Away s)) (_ : IsDomain (Localization.Away s)),
        IsDiscreteValuationRing (Localization.Away s) ∧
        Algebra.Etale O (Localization.Away s) ∧
        Module.FaithfullyFlat O (Localization.Away s) ∧
        IsIso ((stageBase O (Localization.Away s)).fiberToSpecResidueField (closedPoint O)) ∧
        ∃ β : Localization.Away s →ₐ[O] P,
          β.comp (IsScalarTower.toAlgHom O B (Localization.Away s)) = ι ∧
          IsLocalHom β.toRingHom ∧ Function.Injective β := by
  let ψ := ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Ordinary.residuePointAlgHom e he
  let aug : B →ₐ[O] ResidueField O := ψ.comp ι
  have hker : RingHom.ker aug.toRingHom = (maximalIdeal P).comap ι.toRingHom :=
    ZInQ.Contrib.CloudR2NOS.Spreadout.LocalStage.ker_comp_eq_comap ψ
      (ZInQ.Contrib.CloudR2NOS.Spreadout.LocalStage.ker_residuePointAlgHom e he) ι
  obtain ⟨s, hs, hloc, ⟨hlocal, hdom, hdvr, hlh, het, hff, huni, hfib⟩, haug, hfactor⟩ :=
    ZInQ.Contrib.CloudR2NOS.Spreadout.LocalStage.exists_localStage B aug
  letI : IsLocalRing (Localization.Away s) := hlocal
  letI : IsDomain (Localization.Away s) := hdom
  letI : IsDiscreteValuationRing (Localization.Away s) := hdvr
  have hlocP : IsLocalization.AtPrime (Localization.Away s) ((maximalIdeal P).comap ι.toRingHom) := by
    convert hloc using 2
    exact hker.symm
  letI := hlocP
  obtain ⟨β, hβ, hβunique⟩ := hfactor ι hker.symm
  have hβlocal : IsLocalHom β.toRingHom := away_factor_isLocalHom ι s β hβ
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hβinj : Function.Injective β :=
    factor_injective_of_original_uniformizer hOP β π hπ (huni π hπ).1
  have hunit : IsUnit (ι s) := by
    rw [hker] at hs
    exact notMem_maximalIdeal.mp hs
  exact ⟨s, hunit, hlocP, hlocal, hdom, hdvr, het, hff, hfib, β, hβ, hβlocal, hβinj⟩

#print axioms exists_localStage_factor_properties

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
