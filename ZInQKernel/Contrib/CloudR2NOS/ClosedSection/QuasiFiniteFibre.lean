/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section GM11 sub-gap (G6) `QuasiFiniteOnClosedFibre`, PROVED. SOURCE ONLY, UNCOMPILED.
Native HELD. No kernel/ABI/admission grade.

Proof (the composition used in FLT's away theorem, P2M/Sol/S_…exists_away_finiteBySections…, lines
156–198): base change of `𝔔` to the residue field (adapted FLT `exists_baseChange_of_isPullback`, which
gives a CARTESIAN square with `ProjSpace.map C k N`); the base-changed presentation has the same sections
as `𝔔s`, so its map is locally quasi-finite (adapted FLT `locallyQuasiFinite_of_forall_exists_eq_sum_smul`
with coefficients `Pi.single j 1`); quasi-finiteness at points over the closed point then follows from
the cartesian square (adapted FLT `quasiFiniteAt_of_isPullback_of_locallyQuasiFinite`). The adapted FLT
modules are in `ClosedSection/FLTA/` with per-file Apache-2.0 attribution.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step3Gaps
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.FLTA.BaseChange
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.FLTA.LQFSumSmul
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.FLTA.QFAtPullback

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.QuasiFiniteFibre

/-- **(G6) proved.** -/
theorem quasiFiniteOnClosedFibre : QuasiFiniteOnClosedFibre.{u} := by
  intro C _ _ X f _ M _ N 𝔔 𝔔s hσ hfin x hx
  -- the residue field as a `C`-algebra, with `Spec` of its structure map the residue-field point
  let φ : CommRingCat.of C ⟶ (Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C) :=
    Spec.preimage ((Spec (CommRingCat.of C)).fromSpecResidueField (IsLocalRing.closedPoint C))
  letI : Algebra C ↥((Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C)) :=
    φ.hom.toAlgebra
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap C
      ↥((Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C)))) =
      (Spec (CommRingCat.of C)).fromSpecResidueField (IsLocalRing.closedPoint C) := by
    change Spec.map (CommRingCat.ofHom φ.hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  -- the literal closed-fibre square
  have sq : IsPullback (f.fiberι (IsLocalRing.closedPoint C))
      (f.fiberToSpecResidueField (IsLocalRing.closedPoint C)) f
      (Spec.map (CommRingCat.ofHom (algebraMap C
        ↥((Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C))))) := by
    rw [hspec]
    exact IsPullback.of_hasPullback f _
  -- base change of `𝔔` along it, with a cartesian square of maps
  obtain ⟨𝔔K, hσK, -, hsqK⟩ :=
    ZInQ.Contrib.CloudR2NOS.ClosedSection.FLTA.AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback
      sq 𝔔
  -- `𝔔K` and `𝔔s` have the same sections, so `𝔔K.toProj` is locally quasi-finite
  haveI : IsFinite 𝔔s.toProj := hfin
  haveI : LocallyQuasiFinite 𝔔s.toProj := inferInstance
  have hLQF : LocallyQuasiFinite 𝔔K.toProj :=
    ZInQ.Contrib.CloudR2NOS.ClosedSection.FLTA.AlgebraicGeometry.Scheme.Modules.ProjPresentation.locallyQuasiFinite_of_forall_exists_eq_sum_smul
      𝔔s 𝔔K fun j => by
        refine ⟨Pi.single j 1, ?_⟩
        rw [Fintype.sum_eq_single j fun l hl => by
          rw [Pi.single_eq_of_ne hl, map_zero, map_zero, zero_smul]]
        rw [Pi.single_eq_same, map_one, map_one, one_smul, hσ j, hσK j]
        rfl
  haveI := hLQF
  -- `𝔔.toProj` is locally of finite type
  haveI : IsProper (𝔔.toProj ≫ ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π C N) := by
    rw [𝔔.toProj_π]
    infer_instance
  haveI : LocallyOfFiniteType 𝔔.toProj := locallyOfFiniteType_of_comp 𝔔.toProj
    (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π C N)
  -- the point `x` lies on the literal closed fibre
  obtain ⟨z, rfl⟩ : ∃ z, (f.fiberι (IsLocalRing.closedPoint C)).base z = x := by
    have hmem : x ∈ Set.range (f.fiberι (IsLocalRing.closedPoint C)).base := by
      rw [Scheme.Hom.range_fiberι]
      exact hx
    exact hmem
  have hz : 𝔔.toProj.base ((f.fiberι (IsLocalRing.closedPoint C)).base z) =
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.map C
        ↥((Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C)) N).base
          (𝔔K.toProj.base z) := by
    have h := congrArg (fun φ => φ.base z) hsqK.w
    simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using h
  exact ZInQ.Contrib.CloudR2NOS.ClosedSection.FLTA.AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_isPullback_of_locallyQuasiFinite
    hsqK (𝔔K.toProj z) _ hz

end ZInQ.Contrib.CloudR2NOS.ClosedSection.QuasiFiniteFibre
