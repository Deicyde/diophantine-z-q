/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CartierDual_dualBaseChangeLin_bijective_integral
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_CartierDual
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_CharacterClosure
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_CartierDual_dualBaseChangeLin_bijective_integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.dualBaseChangeLin_bijective_integral.{u, v, w}
    (O : Type u) [inst_t1 : CommRing O] (O' : Type v) [inst_t2 : CommRing O'] [inst_t3 : Algebra O O']
    (A : Type w) [inst_t4 : CommRing A] [inst_t5 : HopfAlgebra O A] [inst_t6 : Module.Finite O A] [inst_t7 : Module.Free O A] :
    Function.Bijective (CartierDual.dualBaseChangeLin O O' A) ∧
    CartierDual.dualBaseChangeLin O O' A 1 = 1 ∧
    (∀ x y : O' ⊗[O] CartierDual O A,
        CartierDual.dualBaseChangeLin O O' A (x * y)
          = CartierDual.dualBaseChangeLin O O' A x * CartierDual.dualBaseChangeLin O O' A y) ∧
    (∀ w : O' ⊗[O] CartierDual O A,
        TensorProduct.map (CartierDual.dualBaseChangeLin O O' A) (CartierDual.dualBaseChangeLin O O' A)
            (Coalgebra.comul (R := O') w)
          = Coalgebra.comul (R := O') (CartierDual.dualBaseChangeLin O O' A w)) ∧
    (∀ (g : CartierDual O A) (x : O' ⊗[O] A),
        CartierDual.dualBaseChangeLin O O' A ((1 : O') ⊗ₜ[O] HopfAlgebraStruct.antipode (R := O) g) x
          = CartierDual.dualBaseChangeLin O O' A ((1 : O') ⊗ₜ[O] g) (HopfAlgebraStruct.antipode (R := O') x)) :=
  @_root_.P2MW.S_CartierDual_dualBaseChangeLin_bijective_integral.solution O inst_t1 O' inst_t2 inst_t3 A inst_t4 inst_t5 inst_t6 inst_t7
