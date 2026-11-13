import ZInQKernel.Contrib.TYZGenus.RingClass
open ZInQ.RouteK.Rank5b
example (d : ℕ) [NeZero d] : Normal (QNeg d) (SeparableClosure (QNeg d)) := inferInstance
example (d : ℕ) [NeZero d] : IsAlgClosed (SeparableClosure (QNeg d)) := inferInstance
example (d : ℕ) [NeZero d] : Normal ℚ (SeparableClosure (QNeg d)) := inferInstance
example (d : ℕ) [NeZero d] : Algebra.IsAlgebraic ℚ (SeparableClosure (QNeg d)) := inferInstance
