import ZInQKernel.HDecomp.LeafPush2.T
import ZInQKernel.Contrib.CloudW06PoincareRigidity.T11bExists

/-!
# Corollary: the kernel's T11(b), `ZInQ.LeafPush2.T11b_Rigidity`

Task cloud-w06, 2026-11-14. The kernel's leaf `ZInQ.LeafPush2.T11b_Rigidity`
(`ZInQKernel/HDecomp/LeafPush2/T.lean`, line 56) is `T11bExists` with `∃!` for `∃`. Its existence
half is `T11bExists_proof` (frontier row H-75), and uniqueness holds because base change along
`Spec L ⟶ Spec k` is faithful (`T11bRigidity_unique`, whose statement is the body of
`T11b_Rigidity`). This file only connects the two constants.
-/

namespace ZInQ.Contrib.CloudW06PoincareRigidity

/-- **T11(b), rigidity** (`ZInQ.LeafPush2.T11b_Rigidity`), proved. -/
theorem T11b_Rigidity_proof : ZInQ.LeafPush2.T11b_Rigidity := T11bRigidity_unique

end ZInQ.Contrib.CloudW06PoincareRigidity
