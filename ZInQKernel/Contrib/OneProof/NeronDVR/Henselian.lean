import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Main
import ZInQKernel.Contrib.OneProof.NeronExtAb
import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron
import Mathlib.RingTheory.Henselian

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace NeronDVR

open ZInQ.Contrib.CloudW03NeronSurj.FLT
open NeronModelInfra GoodReductionJacobian
open ZInQ.Contrib.GroupLawNeron (genMap)
open ZInQ.Contrib.CloudR2NeronExistence.Henselian

/-- A Néron model over a henselian DVR, with its generic fibre identified
with the given abelian variety. -/
theorem exists_neron_model_henselian
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (A : PkgI3.AbVar K) :
    ∃ (N : Over (Spec (CommRingCat.of R))),
      CToPrinted.IsNeronModelOver R K N ∧
        Nonempty ((Over.pullback (genMap R K)).obj N ≅ A.X) := by
  let _ : GrpObj (Over.mk A.X.hom) := A.grp
  have : GeometricallyIntegral A.X.hom := A.geomInt
  let law := relativeGroupLawOfGrpObj K A.X.hom
  have abelian : AbelianSchemePropertyBundle K A.X.hom := by
    refine ⟨A.smooth, A.proper, ?_, ⟨law⟩⟩
    intro s
    rw [← A.X.hom.range_fiberι, ← Set.image_univ]
    exact isConnected_univ.image _ (A.X.hom.fiberι s).continuous.continuousOn
  obtain ⟨B, g, _, e, hN, _, he, _⟩ :=
    exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
      (R := R) K law abelian
  let N := Over.mk g
  let eIso := @asIso _ _ _ _ e.1 he
  let ε : (Over.pullback (genMap R K)).obj N ≅ A.X := Over.isoMk eIso e.2
  exact ⟨N, NeronExt.isNeronModelOver_of_bundle R K N hN, ⟨ε⟩⟩

end NeronDVR
