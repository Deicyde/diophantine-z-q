/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.InterfaceD9D10
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D9.FibreUnique

/-! # `FibreUnique_Obligation` is proved (W13, lane D9). -/

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary

theorem fibreUnique_obligation : FibreUnique_Obligation :=
  fun _ 𝒜 _ _ _ _ _ hP hP' => Quotient.sound (isFibreOf_unique 𝒜 hP hP')

end ZInQ.Contrib.CloudB2Shimura.Dictionary

#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.fibreUnique_obligation
