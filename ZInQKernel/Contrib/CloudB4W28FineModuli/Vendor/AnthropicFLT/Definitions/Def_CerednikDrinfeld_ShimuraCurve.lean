/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Apache License 2.0; see LICENSE, NOTICE.upstream and ATTRIBUTION.upstream.md.
W28 compatibility changes: relocated imports; removed imported-only global attribute
suppressions and unused P2M.Util; direct exact solution wrappers; upstream Lake options
made explicit below. Exact bridge cuts, when present, are recorded in SOURCE_MANIFEST.json.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

noncomputable section

open scoped Quaternion TensorProduct MatrixGroups
open IsDedekindDomain NumberField

namespace QuaternionAlgebra

variable (a b : ℚ)

def IsIndefiniteRamifiedExactlyAt (q q' : ℕ) : Prop :=
  (0 < a ∨ 0 < b) ∧
    ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
        ((q : 𝓞 ℚ) ∈ v.asIdeal ∨ (q' : 𝓞 ℚ) ∈ v.asIdeal)

end QuaternionAlgebra
