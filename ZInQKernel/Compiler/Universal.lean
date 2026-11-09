import ZInQKernel.Compiler.Universal.Interpreter
import ZInQKernel.Compiler.Universal.Shape
import ZInQKernel.Compiler.Universal.Grows
import ZInQKernel.Compiler.Universal.Halting
import ZInQKernel.Compiler.Universal.NodeCheck
import ZInQKernel.Compiler.Universal.Specialize
import ZInQKernel.Compiler.Universal.SpecializeShape
import ZInQKernel.Compiler.Universal.PrecisionCircuit
import ZInQKernel.Compiler.Universal.CodeSize
import ZInQKernel.Compiler.Universal.WrapperSize
import ZInQKernel.Compiler.Universal.WrapperCode

/-!
# The universal interpreter and the five-input circuit

Root module of the blueprint chapter `compiler/natural/universal/` (the interpreter literal,
its shape, the universal halting circuit, the five-input natural precision circuit and their
counts) and of `compiler/natural/natural-polynomial-semantics.md`.
-/
