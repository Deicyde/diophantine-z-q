import ZInQKernel.Compiler.Universal.NodeCheck

/-!
# The addition and multiplication bound of the halting circuit

The downstream witness accounting (`Syntax.PrecisionShape`) needs only upper bounds on the
numbers of addition and multiplication nodes of the universal halting circuit, not their exact
values. `HaltingAddMulBound` states these two bounds, in the conventions of
`NodeCheck.HaltingAddMulCheck` (which states the exact counts). It is proved in the kernel as
`NodeCheck.haltingAddMulBound` (`NodeBound/Check.lean`).
-/

namespace ZInQ.Compiler.NodeCheck

open Natural Universal

/-- The addition and multiplication counts of the universal halting circuit are at most
`125,307` and `98,361`. -/
def HaltingAddMulBound : Prop :=
  countKind .add haltingCircuit.nodes ≤ 125307 ∧ countKind .mul haltingCircuit.nodes ≤ 98361

end ZInQ.Compiler.NodeCheck
