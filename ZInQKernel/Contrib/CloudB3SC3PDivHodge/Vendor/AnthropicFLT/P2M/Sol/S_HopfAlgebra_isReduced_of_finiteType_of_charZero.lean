/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_HopfAlgebra_isReduced_of_finiteType_of_charZero
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.Basic
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_HopfAlgebra_isReduced_of_finiteType_of_charZero

set_option maxHeartbeats 3200000
open scoped TensorProduct

theorem solution
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    IsReduced A := by
  let Ω := AlgebraicClosure K

  haveI : IsReduced (Ω ⊗[K] A) :=
    HopfAlgebra.isReduced_of_finiteType_of_isAlgClosed_of_charZero Ω (Ω ⊗[K] A)

  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[K] Ω ⊗[K] A) :=
    Algebra.TensorProduct.includeRight_injective (R := K) (A := Ω) (B := A)
      (algebraMap K Ω).injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[K] Ω ⊗[K] A).toRingHom hinj
