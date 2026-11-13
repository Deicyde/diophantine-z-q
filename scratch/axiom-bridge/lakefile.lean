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

-- These companion libraries are opt-in; root package dependencies are unchanged.
-- Preserve each checked standalone module's name instead of renaming proof imports.
lean_lib TateConsumers where
  roots := #[`TateComparison, `ComposedPointTateSmoke, `TateFreeness, `TateRank,
    `ImportedRhoCont, `NativeContinuity]

lean_lib FrobeniusAdapters where
  srcDir := "../c10-frobenius"
  roots := #[`C10Frobenius, `C10PrimeField, `C10FiniteField, `C10FieldPoints]

lean_lib FrobeniusAdapterChecks where
  srcDir := "../c10-frobenius"
  roots := #[`Check, `CheckPrimeField, `CheckFiniteField, `CheckFieldPoints]
