/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] (hqp : q ≤ p) [Algebra.IsSmoothAt R q]
    (h : Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R]) =
      Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R])) :
    Algebra.IsSmoothAt R p := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq.solution
