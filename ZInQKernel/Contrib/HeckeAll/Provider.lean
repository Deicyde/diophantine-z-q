import ZInQKernel.Contrib.HeckeAll.Continuation
import ZInQKernel.Contrib.GaussFE.FunctionalEquation5

/-! # The provider `ZInQ.Contrib.heckeContinuation`

`L(C_d, s)` has an entire continuation for every `d ≠ 0`: `heckeContinuation_of_gaussPointCount`
(this folder) applied to Gauss's point count, proved in `GaussFE.gaussPointCount`. The two
`GaussPointCount` copies are definitionally equal. -/

theorem ZInQ.Contrib.heckeContinuation : ZInQ.Literature.HeckeContinuation :=
  ZInQ.Contrib.heckeContinuation_of_gaussPointCount ZInQ.Contrib.GaussFE.gaussPointCount
