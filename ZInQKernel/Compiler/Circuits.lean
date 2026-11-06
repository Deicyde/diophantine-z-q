import ZInQKernel.Compiler.Circuits.RegisterMachine
import ZInQKernel.Compiler.Circuits.Construction
import ZInQKernel.Compiler.Circuits.Gadgets
import ZInQKernel.Compiler.Circuits.Compilation
import ZInQKernel.Compiler.Circuits.MacroSemantics
import ZInQKernel.Compiler.Circuits.Exposed
import ZInQKernel.Compiler.Circuits.Circuit
import ZInQKernel.Compiler.Circuits.Builder
import ZInQKernel.Compiler.Circuits.PowerTemplate
import ZInQKernel.Compiler.Circuits.PowerTemplateNodes
import ZInQKernel.Compiler.Circuits.Packed.Digits
import ZInQKernel.Compiler.Circuits.Packed.Masks
import ZInQKernel.Compiler.Circuits.Packed.StateSelection
import ZInQKernel.Compiler.Circuits.Packed.NonzeroIndicator
import ZInQKernel.Compiler.Circuits.Packed.Branches
import ZInQKernel.Compiler.Circuits.Packed.Transitions
import ZInQKernel.Compiler.Circuits.Packed.Construction
import ZInQKernel.Compiler.Circuits.Counts
import ZInQKernel.Compiler.Circuits.Packed.Counts
import ZInQKernel.Compiler.Circuits.Packed.Step
import ZInQKernel.Compiler.Circuits.Packed.Sound
import ZInQKernel.Compiler.Circuits.Packed.Complete
import ZInQKernel.Compiler.Circuits.Packed.Valid
import ZInQKernel.Compiler.Circuits.Packed.Semantics
import ZInQKernel.Compiler.Circuits.Packed.Polynomial
import ZInQKernel.Compiler.Circuits.Scope
import ZInQKernel.Compiler.Circuits.Packed.Scope
import ZInQKernel.Compiler.Circuits.Hierarchical

/-!
# Natural circuits and the packed-history compiler

Root module of the blueprint chapter `compiler/natural/`, sections `formulas/` and `packed/`,
and of the register machines of `compiler/natural/programs/register-machine.md`.
-/
