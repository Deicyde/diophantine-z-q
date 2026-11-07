import ZInQKernel.Compiler.NodeSkeleton.Core
import ZInQKernel.Compiler.NodeSkeleton.Sim.Prims

/-!
# Kernel proof of the addition and multiplication counts of the halting circuit

The node check `NodeCheck.HaltingAddMulCheck` (125,307 additions and 98,361 multiplications in
the node list of the universal halting circuit) is proved by a run of a checking builder, split
into chunks with pinned intermediate states, that simulates the fast builder of
`ZInQKernel/Compiler/NodeCheck/`.
-/
