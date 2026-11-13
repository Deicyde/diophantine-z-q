import ZInQKernel.Multiplication.FormalLog.Algebra
import ZInQKernel.Multiplication.FormalLog.ChainRule
import ZInQKernel.Multiplication.FormalLog.InvDiff
import ZInQKernel.Multiplication.FormalLog.Relations
import ZInQKernel.Multiplication.FormalLog.Identity
import ZInQKernel.Multiplication.FormalLog.Eval
import ZInQKernel.Multiplication.FormalLog.ChordAlgebra
import ZInQKernel.Multiplication.FormalLog.ChordEval
import ZInQKernel.Multiplication.FormalLog.LogAdd
import ZInQKernel.Multiplication.FormalLog.GroupLaw

/-!
# The formal logarithm of `y² = x³ + A x` is a homomorphism

Root module of task `mult-formal-log`: the power-series identity
`log(F(T₁, T₂)) = log(T₁) + log(T₂)` (`Identity.lean`), the evaluation of power series in two
variables (`Eval.lean`), `z(P + Q) = F(z(P), z(Q))` (`ChordEval.lean`), the homomorphism
property of the elliptic logarithm on `W₁(K)` (`LogAdd.lean`, used for `ellLog_add`), and the
formal group law axioms (`GroupLaw.lean`, `formalGroupLaw_exists`).
-/
