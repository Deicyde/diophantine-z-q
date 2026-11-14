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
    `ImportedRhoCont, `NativeContinuity, `NativeEndTrace]

lean_lib FrobeniusAdapters where
  srcDir := "../c10-frobenius"
  roots := #[`C10Frobenius, `C10PrimeField, `C10FiniteField, `C10FieldPoints]

lean_lib FrobeniusAdapterChecks where
  srcDir := "../c10-frobenius"
  roots := #[`Check, `CheckPrimeField, `CheckFiniteField, `CheckFieldPoints]

-- Separate SOURCE-PROPOSAL targets. The original Link module name is retained
-- without putting its source under the repository-root ZInQKernel tree.
-- Full Lake/import-context and released-cache coverage for this layout are pending.
lean_lib OriginalC10Link where
  srcDir := "original-c10"
  roots := #[`ZInQKernel.HDecomp.C10.Link]

lean_lib RationalC10Consumers where
  roots := #[`RationalC10Link]

-- Only positive/specification modules are build roots. The dedicated checkers
-- and expected-failure files must be invoked separately with their own budgets.
lean_lib EndTraceValidation where
  srcDir := "validation/endtrace"
  roots := #[`NativeEndTraceExpectedTypes, `NativeEndTraceCases]

lean_lib RationalC10Validation where
  srcDir := "validation/rational-c10"
  roots := #[`RationalC10ExpectedTypes, `RationalC10Cases]
