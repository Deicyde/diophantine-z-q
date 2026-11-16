/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D34.Surj
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D34.Level

/-!
# W13 dictionary D3/D4: `Dictionary.D34_Obligation`, proved

For every characteristic-`0` field `K`, every `u : FLTL3 K` and every `h : AbVarProps u.1`:

* `q := ⟨iota u.1 h, iota_injective u h⟩ : QMStr (abVarOfFakeEC u.1 h)` satisfies
  `(q.iota a).hom.left = u.1.act (toΛ a)` (definitionally);
* `level3 u h q rfl : Level3 q` satisfies `(toMul (e.eta a)).left = fltLevelPoint u a`
  (definitionally).

Neither D2 nor D5 is used, and no premise is added. The only non-kernel inputs are the FLT
structure fields (`act_*`, `FullLevel.torsion/annihilator`, `comm`) and the FLT source theorems
`etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension` and
`exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing`.
-/

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D34

open ZInQ.Contrib.CloudB2Shimura.Dictionary

/-- **D3/D4.** -/
theorem d34_obligation : D34_Obligation := by
  intro K _ _ u h
  haveI := isDominant_act_three u h
  exact ⟨⟨iota u.1 h, iota_injective u h⟩, fun _ => rfl, level3 u h _ rfl, fun _ => rfl⟩

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D34
