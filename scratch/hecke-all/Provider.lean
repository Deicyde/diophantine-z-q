import ZInQKernel.Contrib.HeckeAll.Continuation
import ZInQKernel.Contrib.GaussFE.FunctionalEquation5

/-! The provider `ZInQ.Contrib.heckeContinuation`, composed from this task's
`heckeContinuation_of_gaussPointCount` and the gauss-proof task's `GaussFE.gaussPointCount`
(the two `GaussPointCount` copies are definitionally equal). This is a scratch file: on integration
it belongs in a Contrib module allowed to import both. -/

theorem ZInQ.Contrib.heckeContinuation : ZInQ.Literature.HeckeContinuation :=
  ZInQ.Contrib.heckeContinuation_of_gaussPointCount ZInQ.Contrib.GaussFE.gaussPointCount

#print axioms ZInQ.Contrib.heckeContinuation
