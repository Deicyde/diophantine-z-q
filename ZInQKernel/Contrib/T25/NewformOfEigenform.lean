import ZInQKernel.HDecomp.ModCurves.C9
import ZInQKernel.Contrib.T25.Bridge

/-!
# T25 proved: `PkgI4.NewformOfEigenform`

Task t25-newform. The leaf T25 (`PkgI4.NewformOfEigenform`, stated in
`ZInQKernel/HDecomp/ModCurves/C9.lean` §7, copied verbatim from
`scratch/h-decomposition/Leaves.lean`) as a closed theorem, from `T25.newformOfEigenform`
(`ZInQKernel/Contrib/T25/Bridge.lean`), which bridges Tau Ceti's
`HeckeRing.GL2.Newform.exists_newform_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul`.
No `sorry`, no `axiom`.
-/

namespace T25

/-- **T25 `PkgI4.NewformOfEigenform`** (Li 1975 Thm 5; Diamond–Shurman Prop. 5.8.4; Miyake
Cor. 4.6.20), proved. -/
theorem newformOfEigenform_leaf : PkgI4.NewformOfEigenform :=
  newformOfEigenform

end T25
