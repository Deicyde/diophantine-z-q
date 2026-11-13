import Lake
open Lake DSL

package axiomBridge where
  leanOptions := #[⟨`autoImplicit, false⟩]

require z_in_q_kernel from "../.."
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"
require Mordell from git
  "https://github.com/AxiomMath/Mordell" @
  "82a30cb7857f6e3cfdb1be91f5533c0ccb57d493"

@[default_target]
lean_lib AxiomBridge
