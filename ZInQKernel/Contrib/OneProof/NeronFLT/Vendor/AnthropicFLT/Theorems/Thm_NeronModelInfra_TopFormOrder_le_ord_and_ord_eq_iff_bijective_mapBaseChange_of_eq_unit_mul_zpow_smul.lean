/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_TopFormOrder_le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_TopFormOrder_le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
    (R' K' O' O F : Type u)
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    (ϖ : R') (hϖ : IsLocalRing.maximalIdeal R' = Ideal.span {ϖ})
    [CommRing O'] [IsDomain O'] [Algebra R' O']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Algebra O' O] [IsScalarTower R' O' O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra O' F] [IsScalarTower O' O F] [IsFractionRing O' F]
    [Algebra K' F] [Algebra R' F] [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    (d : ℕ) (b' : Module.Basis (Fin d) O' (Ω[O'⁄R'])) (b : Module.Basis (Fin d) O (Ω[O⁄R']))
    (m : ℤ) (u : O'ˣ) (σ : ⋀[F]^d (Ω[F⁄K']))
    (hσ : letI := moduleAlong O' F (⋀[F]^d (Ω[F⁄K']))
      σ = (algebraMap O' F (u : O') * algebraMap O' F (algebraMap R' O' ϖ) ^ m) •
        topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b')) :
    m ≤ ord R' K' O d F σ ∧
    (ord R' K' O d F σ = m ↔ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O)) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul.solution
