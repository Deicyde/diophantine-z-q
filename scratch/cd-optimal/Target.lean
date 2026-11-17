import ZInQKernel.Contrib.OneProof.CdOptimal

/-! cd-optimal: verbatim copy of the target `ZInQ.GZOptimal.CdOptimal`
(`ZInQKernel/Contrib/OneProof/GrossZagierOptimal.lean`), checked `rfl` against the original, and the
final theorem applied to it. -/

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve ZInQ.GZDecomp

noncomputable section

namespace ZInQ.CdOptimalTarget

def CdOptimal : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) →
    ∀ L : PeriodPair, ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L →
      ∃ c₀ : ℚ, L.lattice = (ZInQ.GZOptimal.periodLattice f).map (LinearMap.mulLeft ℤ (c₀ : ℂ))

theorem copy_eq : CdOptimal = ZInQ.GZOptimal.CdOptimal := rfl

theorem cdOptimal_target (hW : ZInQ.CdOpt.EtaW32Character) (hT : ZInQ.CdOpt.CdTwistedPeriodOdd) :
    CdOptimal :=
  ZInQ.CdOpt.cdOptimal_of hW hT

end ZInQ.CdOptimalTarget

#print axioms ZInQ.CdOptimalTarget.cdOptimal_target
