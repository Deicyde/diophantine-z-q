import ZInQKernel.Contrib.CloudR2Poincare.L3.B2ProjectionVanishing
import ZInQKernel.Contrib.CloudR2Poincare.L3.B2ZeroFibre
import ZInQKernel.Contrib.CloudR2Poincare.L3.B2SupportDischarged
import ZInQKernel.Contrib.CloudR2Poincare.L2.SeesawFiniteness

/-! Mumford §8 Thm 1, with exactly the three remaining genuine campaign inputs.
Leray, finite support and both actual native model couplings are supplied by
proofs, not by additional model/coefficient/graph assumptions. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L3
#cloudR2LocalInstances
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The unchanged B2 output, conditionally on only global normalized seesaw,
all-degree native B1 vanishing, and the ONE shared family-native square. -/
theorem picZeroPointSurjectivity_of
    (hA : L2.ReducedGlobalNormalizedSeesaw)
    (hB1 : NativePicZeroVanishing.{0})
    (hSquare : L2.NativeTheoremOfTheSquare.{0}) : PicZeroPointSurjectivity.{0} := by
  intro k _ _ _ B M N _ _ hM hN
  by_contra hnot
  let F := mumfordKernelBundle B M N
  have hfinite := L2.finite_translationStabilizer_of_globalSeesaw hA B M hM
  have hfst := higherDirectImages_fst_zero_of_not_in_image hB1 hSquare B M N hN hnot
  have hsnd := higherDirectImages_snd_zero_of_fst_zero_supported B F hfst
    (stabilizerPointSet B M) (stabilizerPointSet_finite B M hfinite)
    (stabilizerPointSet_closed_points B M)
    (higherDirectImages_snd_supported_on_stabilizer hB1 hSquare B M N hfinite)
  let f := (snd B.X B.X).left
  haveI : IsProper f := inferInstanceAs (IsProper (pullback.snd B.X.hom B.X.hom))
  haveI : Flat f := inferInstanceAs (Flat (pullback.snd B.X.hom B.X.hom))
  let b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X := 1
  have hzero := native_fibre_H_zero_of_higherDirectImages_zero B f F
    (fun t => (secondSlice B t).left) (isPullback_secondSlice B) hsnd b 0
  haveI := nontrivial_H_zero_secondSlice B M N
  haveI := hzero
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (α :=
    (((Scheme.Modules.pullback (secondSlice B b).left).obj F).H 0))
  exact hxy (Subsingleton.elim _ _)

end ZInQ.Contrib.CloudR2Poincare.L3
