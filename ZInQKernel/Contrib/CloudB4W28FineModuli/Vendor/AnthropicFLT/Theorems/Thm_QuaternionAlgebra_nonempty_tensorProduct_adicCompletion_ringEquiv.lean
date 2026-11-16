/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Apache License 2.0; see LICENSE, NOTICE.upstream and ATTRIBUTION.upstream.md.
W28 compatibility changes: relocated imports; removed imported-only global attribute
suppressions and unused P2M.Util; direct exact solution wrappers; upstream Lake options
made explicit below. Exact bridge cuts, when present, are recorded in SOURCE_MANIFEST.json.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.Definitions.Def_QuaternionAlgebra_EichlerOrder
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.P2M.Sol.S_QuaternionAlgebra_nonempty_tensorProduct_adicCompletion_ringEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.nonempty_tensorProduct_adicCompletion_ringEquiv
    (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nonempty (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, (a : v.adicCompletion ℚ), (b : v.adicCompletion ℚ)]) := by apply @_root_.P2MW.S_QuaternionAlgebra_nonempty_tensorProduct_adicCompletion_ringEquiv.solution <;> assumption
