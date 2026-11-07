import ZInQKernel.Compiler.NodeBound.Defs
import ZInQKernel.Compiler.NodeBound.OfCheck
import ZInQKernel.Compiler.NodeBound.Up
import ZInQKernel.Compiler.NodeBound.Macros
import ZInQKernel.Compiler.NodeBound.Items
import ZInQKernel.Compiler.NodeBound.Encode

/-!
# The addition and multiplication bound of the universal halting circuit

The interface `NodeCheck.HaltingAddMulBound` (upper bounds on the addition and multiplication
counts of `ℋ`, all that the downstream witness accounting uses) and its consequence from the
exact counts `NodeCheck.HaltingAddMulCheck`.

(Blueprint: `compiler/natural/universal/halting-node-check.md`.)
-/
