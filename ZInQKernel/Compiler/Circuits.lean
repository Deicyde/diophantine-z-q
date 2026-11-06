import ZInQKernel.Compiler.Circuits.RegisterMachine
import ZInQKernel.Compiler.Circuits.Construction
import ZInQKernel.Compiler.Circuits.Gadgets
import ZInQKernel.Compiler.Circuits.Compilation
import ZInQKernel.Compiler.Circuits.MacroSemantics
import ZInQKernel.Compiler.Circuits.Circuit
import ZInQKernel.Compiler.Circuits.Packed.Digits
import ZInQKernel.Compiler.Circuits.Packed.Masks
import ZInQKernel.Compiler.Circuits.Packed.StateSelection
import ZInQKernel.Compiler.Circuits.Packed.NonzeroIndicator
import ZInQKernel.Compiler.Circuits.Packed.Branches
import ZInQKernel.Compiler.Circuits.Packed.Transitions
import ZInQKernel.Compiler.Circuits.Packed.Construction

/-!
# Natural circuits and the packed-history compiler

Root module of the blueprint chapter `compiler/natural/`, sections `formulas/` and `packed/`,
and of the register machines of `compiler/natural/programs/register-machine.md`.
-/
