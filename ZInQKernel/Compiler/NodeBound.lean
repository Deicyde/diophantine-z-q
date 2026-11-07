import ZInQKernel.Compiler.NodeBound.Defs
import ZInQKernel.Compiler.NodeBound.OfCheck
import ZInQKernel.Compiler.NodeBound.Up
import ZInQKernel.Compiler.NodeBound.Macros
import ZInQKernel.Compiler.NodeBound.Items
import ZInQKernel.Compiler.NodeBound.Encode
import ZInQKernel.Compiler.NodeBound.Items67
import ZInQKernel.Compiler.NodeBound.Program67
import ZInQKernel.Compiler.NodeBound.Top
import ZInQKernel.Compiler.NodeBound.Check

/-!
# The addition and multiplication bound of the universal halting circuit

The interface `NodeCheck.HaltingAddMulBound` (upper bounds on the addition and multiplication
counts of `ℋ`, all that the downstream witness accounting uses), its consequence from the exact
counts `NodeCheck.HaltingAddMulCheck` (`OfCheck`), and its kernel proof
`NodeCheck.haltingAddMulBound` (`Check`).

The proof bounds the nodes created by the construction without evaluating it: a node call
creates at most one node of its kind, and none if the node is already present (`Up`, an upper
bound judgment with presence facts). The gadgets and macros are bounded once, for all arguments
(`Macros`), items 1–5 of the packed-history construction for every program (`Items`), items 6
and 7 through symbolic handle lists (`Items67`, `Program67`), and the node encoding with its
repeated right sides (`Encode`). `Top` assembles the bound of the compiled circuit for every
program; `Check` evaluates its program-dependent parts at the universal interpreter by small
kernel computations.

(Blueprint: `compiler/natural/universal/halting-node-check.md`.)
-/
