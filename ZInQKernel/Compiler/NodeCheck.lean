import ZInQKernel.Compiler.NodeCheck.Trie
import ZInQKernel.Compiler.NodeCheck.Builder
import ZInQKernel.Compiler.NodeCheck.Packed
import ZInQKernel.Compiler.NodeCheck.Check
import ZInQKernel.Compiler.NodeCheck.Fast
import ZInQKernel.Compiler.NodeCheck.Consts
import ZInQKernel.Compiler.NodeCheck.Reduced

/-!
# The node check of the universal halting circuit

A verified fast transcription of the hash-consing builder (`NodeCheck.Builder`,
`NodeCheck.Packed`), the equality of its node list with that of `Packed.compiled`
(`NodeCheck.compiled_nodes`), and the Boolean check `NodeCheck.haltingNodeCheckB` with its
soundness theorem `NodeCheck.haltingNodeCheck_of_checkB`.

(Blueprint: `compiler/natural/universal/halting-node-check.md`.)
-/
