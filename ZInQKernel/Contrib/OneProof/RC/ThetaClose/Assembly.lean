import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Neighbour
import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Support

/-! Appendix F on the explicit level order. The stage uses the transported
frame and its actual line-indexed neighbour, with no local comparison inputs. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaClose

open Adelic Eichler ThetaJoin O12StageVal ThetaCoeff ZInQ.Manuscript.RC.Odd

variable {ell N M m : ℕ} [hell : Fact ell.Prime]
variable (h : ell % 4 = 3) (hN : 0 < N) (hcop : N.Coprime ell)
variable (H : DiscriminantData m N ell) (w : ℕ → ℤˣ)

include hell hN H in
theorem exceptionalProduct_ne_zero : 2 * m * N * ell ≠ 0 := by
  have hpos : 0 < m := by have := H.odd; omega
  exact (mul_pos (mul_pos (mul_pos (by decide) hpos) hN) (Fact.out : ell.Prime).pos).ne'

/-- The actual local data of Appendix F on the explicit level order.
This is the specialization of the join with the frame transported to the
indexed generator. -/
def actualPmLocal : PMLocal (Coefficients hN H w) (levelRing h hN) M N ell :=
  let C := levelRoots hN H w
  let hn := exceptionalProduct_ne_zero hN H
  let χ := levelNormCharacter h hN C hn
  let cov := levelNormCovariance h hN C hn (discriminantDisjoint H)
  let D := alignedFrame h hN hcop C hn
  let T := indexedTransport h hN hcop C hn H.odd H.squarefree
  pmLocal h hN hcop C hn χ cov D (weightedNeighbour_of_transport h hN hcop C hn χ cov D T)

theorem actualFilteredSupport :
    ThetaClose.FilteredSupport h hN (levelRoots hN H w) (exceptionalProduct_ne_zero hN H) :=
  filteredSupport h hN _ _ H

variable {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K] [IsSepClosed K]
variable {Ebar : WeierstrassCurve (ZMod ell)} [Ebar.IsElliptic] {ap : ℕ → ℤ}
variable (G : PM.Geometry K (levelRing h hN) N Ebar ap) (d : PM.Evaluation K Ebar M) (L : ℕ)

/-- The actual Schwartz product and norm character are passed to the existing stage. -/
def actualLevelStage : AppF.ThetaStage (StageRing (Coefficients hN H w) M) :=
  pmStage G d L (actualPmLocal h hN hcop H w)

/-- The existing valuation lift on that same stage. -/
def actualLevelValLift : Lift (actualLevelStage h hN hcop H w G d L) :=
  pmValLift G d L (actualPmLocal h hN hcop H w)

end ZInQ.Manuscript.RC.ThetaClose
