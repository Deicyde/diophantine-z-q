/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsDiscreteValuationRing_length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Module

universe u

theorem IsDiscreteValuationRing.length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod
    {R' : Type u} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    (π : R') (hπ : Irreducible π) (r n : ℕ)
    (N'' : Submodule R' ((Fin r → R') × (Fin n → R')))
    (hN : (Ideal.span {π ^ 2} : Ideal R') • N'' ≤ (⊤ : Submodule R' (Fin r → R')).prod ((Ideal.span {π} : Ideal R') • (⊤ : Submodule R' (Fin n → R')))) :
    Module.length R' (Submodule.torsion R' (((Fin r → R') × (Fin n → R')) ⧸ N'')) + Module.finrank R' N'' ≤
      Module.length R' (Submodule.torsion R'
        (↥((⊤ : Submodule R' (Fin r → R')).prod ((Ideal.span {π} : Ideal R') • (⊤ : Submodule R' (Fin n → R')))) ⧸
          ((Ideal.span {π ^ 2} : Ideal R') • N'').comap ((⊤ : Submodule R' (Fin r → R')).prod
            ((Ideal.span {π} : Ideal R') • (⊤ : Submodule R' (Fin n → R')))).subtype)) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod.solution
