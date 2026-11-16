/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_Velu
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VeluOrderTwo
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero
    {K : Type*} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = 3 ∧
      ∃ P : ι → K × K, Function.Injective P ∧
        (∀ i, W.toAffine.Equation (P i).1 (P i).2) ∧ (∀ i, W.veluGy (P i).1 (P i).2 = 0) ∧
        ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero.solution
