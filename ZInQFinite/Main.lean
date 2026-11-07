import ZInQFinite.NodeCheck
import ZInQKernel.Main

/-!
# The main theorem with the node check evaluated natively (milestone 1)

`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_nodeCheck` with the node check
discharged by `haltingNodeCheck_native`: Theorem 1.1 from the four hypotheses, trusting native
evaluation for its one finite computation. Not imported by `ZInQKernel`.
-/

namespace ZInQ

/-- **Theorem 1.1 from the four hypotheses**, with the node statistics of the universal halting
circuit checked by native evaluation (milestone 1). -/
theorem exists_bounded_integer_polynomial_defining_integers_native
    (hH : SixContactEstimate) (hPC : PoleCompleteness)
    (h22 : FixedPrimePattern) (hCAT : CatalogueBound) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_nodeCheck
    Compiler.Universal.haltingNodeCheck_native hH hPC h22 hCAT

end ZInQ
