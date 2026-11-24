import ZInQKernel.Contrib.CloudR2Poincare.Final
import ZInQKernel.Contrib.CloudR2Poincare.L5.D1NativeVanishing

/-!
# H-72: `PoincareComplement` from ONE named input (conditional)

Round 2, 2026-11-15.

B1 (`L3.NativePicZeroVanishing`) is discharged by `L5.NativePicZeroVanishing_proof`. That native proof needs no
Künneth formula. It argues by strong induction on the degree, using:
* the shear rank equality;
* actual flat base change and the higher projection formula for invertible N;
* L3's canonical edge Leray;
* L1's proved reduced global seesaw;
* intrinsic native H⁰ and finiteness.

The only remaining input is the theorem of the square, `L2.NativeTheoremOfTheSquare`.

This module is compiled ONLY by a direct CLI-j1 compile into its own owned output path. It is never built by Lake.
-/

namespace ZInQ.Contrib.CloudR2Poincare

/-- **H-72 from the theorem of the square alone (conditional).** -/
theorem poincareComplement_of_square
    (hSquare : L2.NativeTheoremOfTheSquare.{0}) :
    ZInQ.Contrib.AVB1.PoincareComplement :=
  poincareComplement_of_two_inputs L5.NativePicZeroVanishing_proof hSquare

end ZInQ.Contrib.CloudR2Poincare
