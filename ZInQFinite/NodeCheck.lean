import ZInQKernel.Compiler.NodeCheck

/-!
# The node check of the halting circuit, by native evaluation (milestone 1)

`HaltingNodeCheck` mentions polynomials (the expressions of the builder carry them), so it is
not evaluated directly: the fast builder of `ZInQKernel.Compiler.NodeCheck` keeps only node
indices, and `haltingNodeCheck_of_checkB` reduces the check to the Boolean
`haltingNodeCheckB = true`, which is evaluated natively here.

This library is outside the audited root `ZInQKernel` and is never imported by it.
-/

namespace ZInQ.Compiler.Universal

/-- **The node check of the universal halting circuit**, by native evaluation of the fast
builder. -/
theorem haltingNodeCheck_native : HaltingNodeCheck :=
  NodeCheck.haltingNodeCheck_of_checkB (by native_decide)

end ZInQ.Compiler.Universal
