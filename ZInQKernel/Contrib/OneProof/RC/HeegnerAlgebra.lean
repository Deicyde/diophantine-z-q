import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Coefficients
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Annihilator
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.GroupRing
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Descent
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Precision
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Frobenius
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Transfer
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.LocalDiagrams
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Homotopy
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.InfResMathlib
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Interfaces
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.InterfacesTransfer

/-!
# Lane RC10: the checkable algebra of the finite Heegner descent at 2

Manuscript `diophantine_zq.tex` (11/5), Proposition `ex:arith-finite-heegner` and its proof,
tex lines 2834–3410 (Section 8, "Finite Heegner descent and the derivative identities at two").

The finite algebraic cores of Elliot Glazer's descent are `PROVED`; the cohomological inputs
(Galois cohomology with the coefficients `E[2^a]`, `(T₂E ⊗ A_i)(χ_h Ψ_i)`, `A_i[G]`, Heegner points
and Kolyvagin derivative classes, the inflation–restriction sequence, the integral Shapiro and
transfer maps, local Selmer duality data) are stated as named interfaces in `Interfaces.lean`.

* `Coefficients`: `A_i = (ℤ/2^i)[t]/t^i`, the moving character, the universal quadratic character.
* `Annihilator`: (H1) `e = n + 2`, (H2), the matrix span (tex 2881–2912).
* `GroupRing`: (H5), (H6), (H7) (tex 2969–3002).
* `Descent`: (H8)–(H11), (H10), corestriction compatibility of `d_a` (tex 3004–3086, 3281–3288).
* `Precision`: (H12) and its arithmetic, gap B1-a (tex 3088–3100, 3297–3330).
* `Frobenius`: (H13)–(H19) (tex 3097–3200).
* `Transfer`: (H20), (H21) in degrees 0–2, change of sections, (4.2), gap B1-b (tex 3202–3295).
* `LocalDiagrams`: tame resolution, `res`/`cor` diagonals, adjunction (tex 3297–3336).
* `Homotopy`: contraction transfer, the 3-arrow identity, (H22) witnesses (tex 3337–3406).
* `InfResMathlib`: the injectivity of inflation, exactness at `H¹(G, A)` and the `2^e`-killing
  of (H8) for Mathlib's genuine group cohomology of discrete groups.
* `Interfaces`, `InterfacesTransfer`: the cohomological inputs as named hypotheses, and assembly
  theorems.
-/
