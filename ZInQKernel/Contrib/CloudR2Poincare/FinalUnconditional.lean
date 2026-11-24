import ZInQKernel.Contrib.CloudR2Poincare.FinalB1
import ZInQKernel.Contrib.CloudR2Poincare.L6.NativeSquareProof

/-!
# H-72: unconditional `PoincareComplement`

This file combines two pieces:
* the conditional headline `poincareComplement_of_square`, whose Picard-zero input is
  `L5.NativePicZeroVanishing_proof`; and
* L6's native theorem of the square, `L6.NativeTheoremOfTheSquare_proof`.

The theorem of the square is assembled from:
* L6 `nativeCubeClass_eq_one`;
* L2 `exists_open_cubeFibreHZero_ge_one`;
* L1 `exists_retained_nativeCechFaceModels_with_nativeH01`;
* L3 `cechModuleFaceMap_baseChange_square`.

No model, rank, Picard-zero, square or cube proposition is assumed: both inputs are proved theorems.
-/

namespace ZInQ.Contrib.CloudR2Poincare

/-- **H-72, unconditional:** the original fixed `PoincareComplement` Prop. -/
theorem poincareComplement_proof : ZInQ.Contrib.AVB1.PoincareComplement :=
  poincareComplement_of_square L6.NativeTheoremOfTheSquare_proof.{0}

end ZInQ.Contrib.CloudR2Poincare
