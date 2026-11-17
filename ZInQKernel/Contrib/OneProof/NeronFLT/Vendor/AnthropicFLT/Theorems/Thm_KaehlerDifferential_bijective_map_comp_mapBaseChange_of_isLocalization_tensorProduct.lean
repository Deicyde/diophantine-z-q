/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open TensorProduct

theorem KaehlerDifferential.bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct
    (R A A' B C : Type u) [CommRing R] [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    [Algebra R C] [Algebra A C] [Algebra A' C] [Algebra B C]
    [IsScalarTower R A C] [IsScalarTower R B C] [IsScalarTower A A' C] [IsScalarTower R A' C]
    (M : Submonoid A) [IsLocalization M A']
    [Algebra (A ⊗[R] B) C] [IsScalarTower A (A ⊗[R] B) C]
    (hB : (algebraMap (A ⊗[R] B) C).comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C)
    (N : Submonoid (A ⊗[R] B)) [IsLocalization N C] :
    Function.Bijective
      ((KaehlerDifferential.map R A' C C).restrictScalars C ∘ₗ KaehlerDifferential.mapBaseChange R B C) := by p2m_exact_reverting @_root_.P2MW.S_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct.solution
