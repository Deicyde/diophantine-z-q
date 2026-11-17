import ZInQKernel.Contrib.CloudR2Poincare.L1.ReducedGlobalSeesaw
import ZInQKernel.Contrib.CloudR2Poincare.L2.GlobalFibreTriviality

/-!
# Reduced normalized seesaw after ACTUAL fibre-triviality openness

This is the final topological/gluing reduction, not a HasCube or square model.
The openness hypothesis concerns the literal native residue-fibre predicate;
it must be discharged by the actual two-face cone argument in the final cube.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ZInQ.Contrib.CloudR2Poincare.L1

namespace ZInQ.Contrib.CloudR2Poincare.L6

/-- A normalized actual family is trivial when its ACTUAL fibre-triviality
set is open and nonempty on a connected reduced locally Noetherian parameter.
Native closedness and the PROVED original reduced seesaw discharge the rest. -/
theorem normalizedPicardClass_eq_one_of_open_fibreTriviality
    {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsProper π] [GeometricallyIntegral π]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ π = 𝟙 _)
    (T : Over (Spec (.of k))) [IsLocallyNoetherian T.left]
    [AlgebraicGeometry.IsReduced T.left] [ConnectedSpace T.left]
    (L : (pullback π T.hom).Pic)
    (hNorm : Scheme.Pic.map (sectionBaseChange π σ hσ T) L = 1)
    (hOpen : IsOpen (ZInQ.Contrib.CloudR2Poincare.L2.fibrePicardTrivialitySet
      (pullback.snd π T.hom) L))
    (hNonempty : (ZInQ.Contrib.CloudR2Poincare.L2.fibrePicardTrivialitySet
      (pullback.snd π T.hom) L).Nonempty) : L = 1 := by
  have hClosed := ZInQ.Contrib.CloudR2Poincare.L2.isClosed_fibrePicardTrivialitySet
    (pullback.snd π T.hom) L
  have hAll : ZInQ.Contrib.CloudR2Poincare.L2.fibrePicardTrivialitySet
      (pullback.snd π T.hom) L = Set.univ :=
    IsClopen.eq_univ ⟨hClosed, hOpen⟩ hNonempty
  apply normalizedPicardClass_eq_one_of_residueFibres_reduced π σ hσ T L hNorm
  intro t
  have ht : t ∈ ZInQ.Contrib.CloudR2Poincare.L2.fibrePicardTrivialitySet
      (pullback.snd π T.hom) L := hAll ▸ Set.mem_univ t
  exact ht

end ZInQ.Contrib.CloudR2Poincare.L6
