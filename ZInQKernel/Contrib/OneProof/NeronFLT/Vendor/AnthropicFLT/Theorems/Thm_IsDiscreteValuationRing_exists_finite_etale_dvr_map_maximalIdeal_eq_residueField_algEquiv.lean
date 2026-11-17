/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v

theorem IsDiscreteValuationRing.exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k' : Type v) [Field k'] [Algebra (IsLocalRing.ResidueField R) k'] [FiniteDimensional (IsLocalRing.ResidueField R) k']
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) k'] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (_ : IsLocalHom (algebraMap R R')),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' ∧
      Nonempty (k' ≃ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R') := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv.solution
