import ZInQKernel.Model.Descent.PointCounts
import ZInQKernel.Model.Descent.Factor

/-!
# No odd torsion in `E(K₀)`

Blueprint: `model/descent/torsion.md` (odd part), via `model/descent/reduction-torsion.md`.
-/

namespace ZInQ

/-- `E(K₀)` has no point of odd prime order. -/
theorem odd_prime_torsion_E (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (P : genCurve.toAffine.Point)
    (h : q • P = 0) : P = 0 := by
  sorry

end ZInQ
