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
NEW EDITION (lane C4, 2026-11-17; deliverable build a Parent compile probe: 51:8, 55:4; 54:9 cascade). Statements unchanged.
* the literal closed-fibre square is obtained by `erw [hspec]` (default transparency): the target is not type-correct at
  instance transparency (the closed point used as a point of `Spec C`), so `rw` found no key;
* the base-change lemma gets its residue-field algebra `A` explicitly, so its `[Algebra C A]` argument is the local
  `φ.hom.toAlgebra` instance on `↥(residueField (closedPoint C))` rather than a search on the unfolded
  `IsLocalRing.ResidueField (stalk …)`.
EDITION 3 (lane C4, 2026-11-17; deliverable build a Parent compile probe: 63:4; 62:9 cascade). Statements unchanged: the
51/55 fixes held; the residue-field algebra is now passed to the base-change lemma EXPLICITLY (`@… C K _ _ φ.hom.toAlgebra …`)
— the same local `φ.hom.toAlgebra` instance — since instance search did not match it (two ring-structure paths on the
residue field: the CommRingCat one used by the local instance and the field one found by search).
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
    first
    | (erw [hspec]; exact IsPullback.of_hasPullback f _)
    | exact hspec ▸ IsPullback.of_hasPullback f _
    | (rw [hspec]; exact IsPullback.of_hasPullback f _)
  -- base change of `𝔔` along it, with a cartesian square of maps
  obtain ⟨𝔔K, hσK, -, hsqK⟩ :=
    @ZInQ.Contrib.CloudR2NOS.ClosedSection.FLTA.AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback
      C ↥((Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C)) _ _ φ.hom.toAlgebra
      _ _ _ _ _ sq _ _ 𝔔
  -- `𝔔K` and `𝔔s` have the same sections, so `𝔔K.toProj` is locally quasi-finite
  haveI : IsFinite 𝔔s.toProj := hfin
  haveI : LocallyQuasiFinite 𝔔s.toProj := inferInstance
  have hmapOne {R S : CommRingCat.{u}} (g : R ⟶ S) : g (1 : R) = (1 : S) :=
    g.hom.map_one'
  have hLQF : LocallyQuasiFinite 𝔔K.toProj :=
    ZInQ.Contrib.CloudR2NOS.ClosedSection.FLTA.AlgebraicGeometry.Scheme.Modules.ProjPresentation.locallyQuasiFinite_of_forall_exists_eq_sum_smul
      𝔔s 𝔔K fun j => by
        refine ⟨Pi.single j 1, ?_⟩
        rw [Fintype.sum_eq_single j fun l hl => by
          rw [Pi.single_eq_of_ne hl, map_zero, map_zero, zero_smul]]
        erw [Pi.single_eq_same, hmapOne, hmapOne, one_smul, hσ j, hσK j] <;> rfl
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
      erw [Scheme.Hom.range_fiberι f (IsLocalRing.closedPoint C)]
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
