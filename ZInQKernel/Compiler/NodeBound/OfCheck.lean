import ZInQKernel.Compiler.NodeBound.Defs
import ZInQKernel.Compiler.NodeCheck.Reduced

/-!
# The bound from the exact counts

The exact addition and multiplication counts `HaltingAddMulCheck` give the bound
`HaltingAddMulBound`.
-/

namespace ZInQ.Compiler.NodeCheck

theorem haltingAddMulBound_of_check (h : HaltingAddMulCheck) : HaltingAddMulBound :=
  ⟨h.1.le, h.2.le⟩

end ZInQ.Compiler.NodeCheck
