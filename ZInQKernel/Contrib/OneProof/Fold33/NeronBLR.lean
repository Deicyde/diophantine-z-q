import ZInQKernel.Contrib.OneProof.NeronBaseChangeBLR72
import ZInQKernel.Contrib.OneProof.NeronBaseChangeStrictHenselization

/-!
# The research leaf `blr_7_2_1` is proved (leaf-fold33)

`DictModels.NeronBLR72.BLR_7_2_1` (BLR, *Néron models*, §7.2 Thm. 1 in the chain's form) is by definition
`ReductGlue.NeronBaseChangeUnramifiedDVR`. Task neron-sh-proof proved that statement outright
(`NeronSH.neronBaseChangeUnramifiedDVR_proof`, any residue field, `K'/K` separable algebraic, no strict
henselization), so the leaf is discharged with no new leaf.
-/

namespace ZInQ.Contrib.OneProof.Fold33

/-- BLR §7.2 Thm. 1 in the chain's form, proved: the neron-sh-proof theorem, unfolded through the definition of
`BLR_7_2_1`. -/
theorem blr_7_2_1_proof : DictModels.NeronBLR72.BLR_7_2_1 :=
  NeronSH.neronBaseChangeUnramifiedDVR_proof

end ZInQ.Contrib.OneProof.Fold33
