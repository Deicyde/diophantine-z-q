import ZInQKernel.Compiler.Circuits.PowerTemplate

/-!
# Node statistics of the power template

A kernel computation: the node list of the power template has `474` nodes, its root is the last
node and its variable count is `82`, as in the saved precision polynomial
(`construction/precision-natural-polynomial.json`, template `0`). The full node list was also
compared with the saved one during development.
-/

namespace ZInQ.Compiler.Natural

set_option maxRecDepth 100000 in
theorem powerTemplateCircuit_stats :
    (powerTemplateCircuit.nodes.length, powerTemplateCircuit.root, powerTemplateCircuit.varCount)
      = (474, 473, 82) := by
  decide +kernel

end ZInQ.Compiler.Natural
