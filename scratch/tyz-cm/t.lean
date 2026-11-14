import ZInQKernel.Contrib.TYZGenus.ShimuraRecip
open ZInQ.RouteK.Rank5b NumberField
def oneN (n : ℕ) : QNeg n := ⟨1 / 32, 0⟩
example (n : ℕ) [NeZero n] (x : QNeg n) : (x * oneN n).re = x.re / 32 := by
  simp [oneN]
example (n : ℕ) [NeZero n] (x : QNeg n) : (x * oneN n).re = x.re / 32 := by
  simp only [oneN, QuadraticAlgebra.re_mul]
  ring
