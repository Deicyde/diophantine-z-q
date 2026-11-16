/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D7.Universal
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D7.BaseChange
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D7.Rigid
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D7.Dim

/-!
# W13 dictionary D7: `Dictionary.D7_Obligation`, proved

`d7_of_inputs` (`Universal.lean`) applied to `bcInput`, `rigidInput` and `dimInput`, which are
proved from the FLT source theorems listed in their files. There is no hypothesis.
-/

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D7

open ZInQ.Contrib.CloudB2Shimura.Dictionary

/-- **D7.** -/
theorem d7_obligation : D7_Obligation := d7_of_inputs bcInput rigidInput dimInput

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D7
