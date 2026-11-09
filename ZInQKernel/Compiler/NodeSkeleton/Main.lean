import ZInQKernel.Compiler.NodeSkeleton.Final
import ZInQKernel.Compiler.NodeCheck.Reduced

/-!
# The node check of the halting circuit, by the kernel

`haltingAddMulCheck`: the node list of the universal halting circuit has `125,307` addition
and `98,361` multiplication nodes. It is the count of the fast run (`NodeSkeleton.fast_counts`),
transferred to the circuit by `NodeCheck.compiled_nodes`. With the three items proved
symbolically in `NodeCheck/Reduced.lean`, this gives the full `HaltingNodeCheck`.
-/

namespace ZInQ.Compiler.NodeCheck

open Natural Universal

/-- **The addition and multiplication counts of the halting circuit**, checked by the kernel
(no native evaluation). -/
theorem haltingAddMulCheck : HaltingAddMulCheck := by
  have h := NodeSkeleton.fast_counts
  unfold NodeSkeleton.Goal at h
  rewrite [← NodeSkeleton.fastNodesRevK_bind] at h
  unfold HaltingAddMulCheck
  rewrite [show haltingCircuit = Packed.compiled interpreter 204 2 from rfl, compiled_nodes,
    ← fastNodesRevK_eq, countKind_reverse, countKind_reverse]
  exact h

/-- **The node check of the halting circuit**, checked by the kernel. -/
theorem haltingNodeCheck : Universal.HaltingNodeCheck :=
  haltingNodeCheck_of_addMul haltingAddMulCheck

end ZInQ.Compiler.NodeCheck
