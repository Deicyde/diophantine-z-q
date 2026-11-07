import ZInQKernel.Compiler.Programs.PrecisionCorrect
import ZInQKernel.Compiler.Programs.LoweringCorrect
import ZInQKernel.Compiler.Programs.Wrapper

/-!
# The precision machine halts exactly on acceptance

Blueprint: `compiler/natural/programs/precision-machine.md`.

`M_prec = low(S_prec)` (`precisionMachine`): for every `c ∈ ℕ⁵`, `M_prec` halts on `c` iff it
accepts `c` iff `accepts(c)`; when `accepts(c)` fails the run never halts (it ends in the
permanent self-loop), although the ideal program is total.
-/

namespace ZInQ.Compiler.IR

open Precision

/-- `M_prec` halts on `c` iff `accepts(c)`. -/
theorem precisionMachine_halts_iff (c : Fin 5 → ℕ) :
    precisionMachine.HaltsOn c ↔ accepts c :=
  (lower_halts_iff precisionProgram precisionProgram_wf c).trans (precisionProgram_accepts_iff c)

/-- `M_prec` accepts `c` iff `accepts(c)`. -/
theorem precisionMachine_accepts_iff (c : Fin 5 → ℕ) :
    precisionMachine.Accepts c ↔ accepts c :=
  (lower_accepts_iff precisionProgram precisionProgram_wf c).trans (precisionProgram_accepts_iff c)

/-- **The precision machine halts exactly on acceptance.** -/
theorem precisionMachine_correct (c : Fin 5 → ℕ) :
    (precisionMachine.HaltsOn c ↔ precisionMachine.Accepts c) ∧
      (precisionMachine.Accepts c ↔ accepts c) :=
  ⟨(precisionMachine_halts_iff c).trans (precisionMachine_accepts_iff c).symm,
    precisionMachine_accepts_iff c⟩

/-- When `accepts(c)` fails, the run of `M_prec` never halts. -/
theorem precisionMachine_not_halts (c : Fin 5 → ℕ) (h : ¬ accepts c) :
    ¬ precisionMachine.HaltsOn c := fun hh => h ((precisionMachine_halts_iff c).mp hh)

end ZInQ.Compiler.IR
